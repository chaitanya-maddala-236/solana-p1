/**
 * Mini Solana Validator
 * Implements a single-node in-memory Solana-compatible JSON-RPC server.
 * Supports: System Program, SPL Token Program, Associated Token Account Program
 */
import express, { Request, Response } from "express";
import { createHash } from "crypto";

const _require = require;
// eslint-disable-next-line @typescript-eslint/no-var-requires
const nacl = _require("tweetnacl") as typeof import("tweetnacl");

// ─── Native Base58 ────────────────────────────────────────────────────────────
const B58_ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
const B58_MAP: Record<string, number> = {};
for (let i = 0; i < B58_ALPHABET.length; i++) B58_MAP[B58_ALPHABET[i]] = i;

function b58enc(input: Buffer | Uint8Array): string {
  const buf = input instanceof Buffer ? input : Buffer.from(input);
  if (buf.length === 0) return "";
  let leading = 0;
  while (leading < buf.length && buf[leading] === 0) leading++;
  let n = 0n;
  for (const byte of buf) n = n * 256n + BigInt(byte);
  let result = "";
  while (n > 0n) { result = B58_ALPHABET[Number(n % 58n)] + result; n = n / 58n; }
  return "1".repeat(leading) + result;
}

function b58dec(input: string): Buffer {
  if (!input || input.length === 0) return Buffer.alloc(0);
  let leading = 0;
  while (leading < input.length && input[leading] === "1") leading++;
  let n = 0n;
  for (const ch of input) {
    const val = B58_MAP[ch];
    if (val === undefined) throw new Error(`Invalid base58 character: ${ch}`);
    n = n * 58n + BigInt(val);
  }
  const bytes: number[] = [];
  while (n > 0n) { bytes.unshift(Number(n & 0xffn)); n = n >> 8n; }
  return Buffer.from([...new Array(leading).fill(0), ...bytes]);
}

// ─── Constants ────────────────────────────────────────────────────────────────
const SYSTEM_PROGRAM_ID  = "11111111111111111111111111111111";
const TOKEN_PROGRAM_ID   = "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA";
const ATA_PROGRAM_ID     = "ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL";
const TOKEN_ACCOUNT_SIZE = 165;
const MINT_SIZE          = 82;

function rentExempt(dataSize: number): number {
  return Math.ceil((dataSize + 128) * 3480);
}

// ─── Ledger ───────────────────────────────────────────────────────────────────
interface Account {
  lamports:   number;
  owner:      string;
  data:       Buffer;
  executable: boolean;
}

const ledger       = new Map<string, Account>();
const confirmedTxs = new Map<string, { slot: number; err: string | null }>();

// FIX 1: Replace simple Set with Map tracking lastValidBlockHeight per blockhash.
// Real Solana rejects transactions whose blockhash's lastValidBlockHeight < currentSlot.
interface BlockhashInfo { lastValidBlockHeight: number; }
const blockhashRegistry = new Map<string, BlockhashInfo>();

let slot = 100;

function seedProgram(pk: string, owner: string) {
  ledger.set(pk, { lamports: 1_000_000_000, owner, data: Buffer.alloc(0), executable: true });
}
seedProgram(SYSTEM_PROGRAM_ID, "NativeLoader1111111111111111111111111111111");
seedProgram(TOKEN_PROGRAM_ID,  "BPFLoader2111111111111111111111111111111111");
seedProgram(ATA_PROGRAM_ID,    "BPFLoader2111111111111111111111111111111111");

// ─── Account helpers ──────────────────────────────────────────────────────────
function touchAcct(pk: string): Account {
  if (!ledger.has(pk)) {
    ledger.set(pk, { lamports: 0, owner: SYSTEM_PROGRAM_ID, data: Buffer.alloc(0), executable: false });
  }
  return ledger.get(pk)!;
}

function accountExists(pk: string): boolean {
  const a = ledger.get(pk);
  return !!a && (a.lamports > 0 || a.data.length > 0);
}

function mustAcct(pk: string): Account {
  const a = ledger.get(pk);
  if (!a) throw mkErr(-32003, `Account not found: ${pk}`);
  return a;
}

function mkErr(code: number, message: string): { code: number; message: string } {
  return { code, message };
}

// ─── Blockhash ─────────────────────────────────────────────────────────────────
function freshBlockhash(): string {
  const h = b58enc(nacl.randomBytes(32));
  blockhashRegistry.set(h, { lastValidBlockHeight: slot + 300 });
  return h;
}
// Pre-generate blockhashes so tests can start immediately
for (let i = 0; i < 20; i++) freshBlockhash();

let sigNonce = 0;
function fakeSig(): string {
  const buf = Buffer.alloc(64);
  buf.writeBigUInt64LE(BigInt(++sigNonce), 0);
  buf.writeBigUInt64LE(BigInt(Date.now()), 8);
  return b58enc(buf);
}

// ─── Token Account layout (165 bytes) ─────────────────────────────────────────
function encodeTA(mint: string, owner: string, amount: bigint, state = 1): Buffer {
  const buf = Buffer.alloc(TOKEN_ACCOUNT_SIZE, 0);
  b58dec(mint).copy(buf, 0);
  b58dec(owner).copy(buf, 32);
  buf.writeBigUInt64LE(amount, 64);
  buf[108] = state;
  return buf;
}

function decodeTA(data: Buffer) {
  if (data.length < TOKEN_ACCOUNT_SIZE) throw mkErr(-32002, "Not a token account (too small)");
  return {
    mint:   b58enc(data.subarray(0, 32)),
    owner:  b58enc(data.subarray(32, 64)),
    amount: data.readBigUInt64LE(64),
    state:  data[108],
  };
}

// ─── Mint layout (82 bytes) ────────────────────────────────────────────────────
function encodeMint(mintAuth: string | null, decimals: number, supply: bigint, freezeAuth: string | null): Buffer {
  const buf = Buffer.alloc(MINT_SIZE, 0);
  if (mintAuth) { buf.writeUInt32LE(1, 0); b58dec(mintAuth).copy(buf, 4); }
  buf.writeBigUInt64LE(supply, 36);
  buf[44] = decimals;
  buf[45] = 1;
  if (freezeAuth) { buf.writeUInt32LE(1, 46); b58dec(freezeAuth).copy(buf, 50); }
  return buf;
}

function decodeMint(data: Buffer) {
  if (data.length < MINT_SIZE) throw mkErr(-32002, "Not a mint (too small)");
  const mintAuthOpt = data.readUInt32LE(0);
  const freezeOpt   = data.readUInt32LE(46);
  return {
    mintAuth:      mintAuthOpt ? b58enc(data.subarray(4, 36))  : null as string | null,
    supply:        data.readBigUInt64LE(36),
    decimals:      data[44],
    isInitialized: data[45] === 1,
    freezeAuth:    freezeOpt  ? b58enc(data.subarray(50, 82)) : null as string | null,
  };
}

// ─── Ed25519 on-curve check ────────────────────────────────────────────────────
const ED_P = (2n ** 255n) - 19n;
const ED_D = 37095705934669439343138083508754565189542113879843219016388785533085940283555n;

function modPow(base: bigint, exp: bigint, mod: bigint): bigint {
  let result = 1n;
  base = base % mod;
  while (exp > 0n) {
    if (exp & 1n) result = result * base % mod;
    exp >>= 1n;
    base = base * base % mod;
  }
  return result;
}

function pointIsOnCurve(bytes: Buffer): boolean {
  try {
    const buf = Buffer.from(bytes);
    const signBit = (buf[31] & 0x80) !== 0;
    buf[31] &= 0x7f;
    let y = 0n;
    for (let i = 31; i >= 0; i--) y = (y << 8n) | BigInt(buf[i]);
    if (y >= ED_P) return false;
    const y2  = y * y % ED_P;
    const num = ((y2 - 1n) % ED_P + ED_P) % ED_P;
    const den = (ED_D * y2 + 1n) % ED_P;
    const x2  = num * modPow(den, ED_P - 2n, ED_P) % ED_P;
    if (x2 === 0n) return !signBit;
    return modPow(x2, (ED_P - 1n) / 2n, ED_P) === 1n;
  } catch { return false; }
}

// ─── PDA Derivation ────────────────────────────────────────────────────────────
function createProgramAddress(seeds: Buffer[], programId: string): string {
  const h = createHash("sha256");
  for (const s of seeds) h.update(s);
  h.update(b58dec(programId));
  h.update(Buffer.from("ProgramDerivedAddress"));
  const candidate = h.digest();
  if (pointIsOnCurve(candidate)) throw new Error("Seed generates on-curve address");
  return b58enc(candidate);
}

function findProgramAddress(seeds: Buffer[], programId: string): [string, number] {
  for (let nonce = 255; nonce >= 0; nonce--) {
    try {
      const addr = createProgramAddress([...seeds, Buffer.from([nonce])], programId);
      return [addr, nonce];
    } catch { /* try next nonce */ }
  }
  throw new Error("Could not find valid PDA");
}

function deriveATA(owner: string, mint: string): string {
  const [addr] = findProgramAddress(
    [b58dec(owner), b58dec(TOKEN_PROGRAM_ID), b58dec(mint)],
    ATA_PROGRAM_ID
  );
  return addr;
}

// ─── Transaction wire format parsing ──────────────────────────────────────────
interface TxAccount { pubkey: string; isSigner: boolean; isWritable: boolean; }
interface TxInstruction { programId: string; accounts: TxAccount[]; data: Buffer; }
interface ParsedTx {
  signatures:   Buffer[];
  signerKeys:   string[];
  allKeys:      string[];
  instructions: TxInstruction[];
  blockhash:    string;
  messageBytes: Buffer;
}

function readCU16(buf: Buffer, off: number): [number, number] {
  let val = 0, shift = 0;
  for (;;) {
    if (off >= buf.length) throw new Error("Buffer underflow reading compact-u16");
    const b = buf[off++];
    val |= (b & 0x7f) << shift;
    if (!(b & 0x80)) break;
    shift += 7;
  }
  return [val, off];
}

function parseLegacyMessage(buf: Buffer, startOff: number) {
  let off = startOff;
  const numSigRequired      = buf[off++];
  const numReadonlySigned   = buf[off++];
  const numReadonlyUnsigned = buf[off++];
  let numKeys: number;
  [numKeys, off] = readCU16(buf, off);
  const allKeys: string[] = [];
  for (let i = 0; i < numKeys; i++) {
    if (off + 32 > buf.length) throw new Error("Buffer underflow reading account key");
    allKeys.push(b58enc(buf.subarray(off, off + 32)));
    off += 32;
  }
  if (off + 32 > buf.length) throw new Error("Buffer underflow reading blockhash");
  const blockhash = b58enc(buf.subarray(off, off + 32));
  off += 32;
  let numInstrs: number;
  [numInstrs, off] = readCU16(buf, off);
  const instructions: TxInstruction[] = [];
  for (let i = 0; i < numInstrs; i++) {
    if (off >= buf.length) throw new Error("Buffer underflow reading instruction");
    const pidIdx = buf[off++];
    if (pidIdx >= allKeys.length) throw new Error(`Invalid program id index: ${pidIdx}`);
    const programId = allKeys[pidIdx];
    let numAccs: number;
    [numAccs, off] = readCU16(buf, off);
    const accounts: TxAccount[] = [];
    for (let j = 0; j < numAccs; j++) {
      if (off >= buf.length) throw new Error("Buffer underflow reading account index");
      const idx = buf[off++];
      if (idx >= allKeys.length) throw new Error(`Invalid account index: ${idx}`);
      const isSigner  = idx < numSigRequired;
      const isWritable =
        idx < (numSigRequired - numReadonlySigned) ||
        (idx >= numSigRequired && idx < (numKeys - numReadonlyUnsigned));
      accounts.push({ pubkey: allKeys[idx], isSigner, isWritable });
    }
    let dataLen: number;
    [dataLen, off] = readCU16(buf, off);
    if (off + dataLen > buf.length) throw new Error("Buffer underflow reading instruction data");
    const data = Buffer.from(buf.subarray(off, off + dataLen));
    off += dataLen;
    instructions.push({ programId, accounts, data });
  }
  return { numSigRequired, numReadonlySigned, numReadonlyUnsigned, allKeys, blockhash, instructions, endOffset: off };
}

function parseTx(raw: Buffer): ParsedTx {
  let off = 0;
  let numSigs: number;
  [numSigs, off] = readCU16(raw, off);
  const signatures: Buffer[] = [];
  for (let i = 0; i < numSigs; i++) {
    if (off + 64 > raw.length) throw new Error("Buffer underflow reading signature");
    signatures.push(Buffer.from(raw.subarray(off, off + 64)));
    off += 64;
  }
  const msgStart = off;
  let isVersioned = false;
  // Versioned transactions have a prefix byte with high bit set (e.g. 0x80 = version 0).
  // Legacy transactions start with numRequiredSignatures which is always small (< 128).
  if (raw[off] !== undefined && (raw[off] & 0x80) !== 0) { isVersioned = true; off++; }
  const parsed = parseLegacyMessage(raw, off);
  // For versioned transactions the full signed payload extends to end of buffer
  // (includes address lookup table entries after instructions).
  // For legacy transactions it ends exactly at parsed.endOffset.
  const messageBytes = Buffer.from(isVersioned ? raw.subarray(msgStart) : raw.subarray(msgStart, parsed.endOffset));
  return {
    signatures,
    signerKeys:   parsed.allKeys.slice(0, parsed.numSigRequired),
    allKeys:      parsed.allKeys,
    instructions: parsed.instructions,
    blockhash:    parsed.blockhash,
    messageBytes,
  };
}

// ─── Signature verification ────────────────────────────────────────────────────
function verifySigs(tx: ParsedTx): void {
  if (tx.signatures.length < tx.signerKeys.length) {
    throw mkErr(-32003, `Not enough signatures: need ${tx.signerKeys.length}, got ${tx.signatures.length}`);
  }
  for (let i = 0; i < tx.signerKeys.length; i++) {
    const sig    = tx.signatures[i];
    const pubkey = tx.signerKeys[i];
    if (!sig || sig.length !== 64) throw mkErr(-32003, `Missing or malformed signature at index ${i}`);
    if (sig.every(b => b === 0))   throw mkErr(-32003, `Zero (placeholder) signature for signer ${pubkey}`);
    const pubBytes = b58dec(pubkey);
    if (pubBytes.length !== 32) throw mkErr(-32003, `Invalid public key: ${pubkey}`);
    const valid = nacl.sign.detached.verify(tx.messageBytes, new Uint8Array(sig), new Uint8Array(pubBytes));
    if (!valid) throw mkErr(-32003, `Invalid signature for ${pubkey}`);
  }
}

// ─── Instruction execution ─────────────────────────────────────────────────────
let currentSigners = new Set<string>();

function requireSigner(pk: string, role = "account"): void {
  if (!currentSigners.has(pk)) throw mkErr(-32003, `${role} (${pk}) must be a signer`);
}

// ── System Program ────────────────────────────────────────────────────────────
function execSystem(instr: TxInstruction): void {
  if (instr.data.length < 4) throw mkErr(-32003, "System: instruction data too short");
  const disc = instr.data.readUInt32LE(0);
  switch (disc) {
    case 0: {
      if (instr.data.length < 52) throw mkErr(-32003, "CreateAccount: data too short");
      const lamports = Number(instr.data.readBigUInt64LE(4));
      const space    = Number(instr.data.readBigUInt64LE(12));
      const owner    = b58enc(instr.data.subarray(20, 52));
      const payer    = instr.accounts[0].pubkey;
      const newPk    = instr.accounts[1].pubkey;
      requireSigner(payer, "payer");
      requireSigner(newPk, "new account");
      if (accountExists(newPk)) throw mkErr(-32003, `Account already exists: ${newPk}`);
      const payerAcct = touchAcct(payer);
      if (payerAcct.lamports < lamports) throw mkErr(-32003, `Payer insufficient funds: need ${lamports}, have ${payerAcct.lamports}`);
      payerAcct.lamports -= lamports;
      ledger.set(newPk, { lamports, owner, data: Buffer.alloc(space), executable: false });
      break;
    }
    case 1: {
      if (instr.data.length < 36) throw mkErr(-32003, "Assign: data too short");
      const newOwner = b58enc(instr.data.subarray(4, 36));
      requireSigner(instr.accounts[0].pubkey, "account");
      touchAcct(instr.accounts[0].pubkey).owner = newOwner;
      break;
    }
    case 2: {
      if (instr.data.length < 12) throw mkErr(-32003, "Transfer: data too short");
      const lamports = Number(instr.data.readBigUInt64LE(4));
      const from     = instr.accounts[0].pubkey;
      const to       = instr.accounts[1].pubkey;
      requireSigner(from, "from");
      const fromAcct = touchAcct(from);
      if (fromAcct.lamports < lamports) throw mkErr(-32003, `Insufficient SOL: need ${lamports}, have ${fromAcct.lamports}`);
      fromAcct.lamports -= lamports;
      touchAcct(to).lamports += lamports;
      break;
    }
    case 3: {
      const payer = instr.accounts[0].pubkey;
      const newPk = instr.accounts[1].pubkey;
      requireSigner(payer, "payer");
      if (accountExists(newPk)) throw mkErr(-32003, `Account already exists: ${newPk}`);
      const seedLen = instr.data.readUInt32LE(36);
      const base    = 40 + seedLen;
      if (instr.data.length < base + 20) throw mkErr(-32003, "CreateAccountWithSeed: data too short");
      const lamports = Number(instr.data.readBigUInt64LE(base));
      const space    = Number(instr.data.readBigUInt64LE(base + 8));
      const owner    = b58enc(instr.data.subarray(base + 16, base + 48));
      const payerAcct = touchAcct(payer);
      if (payerAcct.lamports < lamports) throw mkErr(-32003, "Insufficient funds");
      payerAcct.lamports -= lamports;
      ledger.set(newPk, { lamports, owner, data: Buffer.alloc(space), executable: false });
      break;
    }
    default:
      throw mkErr(-32003, `Unknown system instruction: ${disc}`);
  }
}

// ── SPL Token Program ─────────────────────────────────────────────────────────
function execToken(instr: TxInstruction): void {
  if (instr.data.length < 1) throw mkErr(-32003, "Token: empty instruction");
  const disc = instr.data[0];
  switch (disc) {
    case 0: {
      if (instr.data.length < 67) throw mkErr(-32003, "InitializeMint: data too short");
      const decimals   = instr.data[1];
      const mintAuth   = b58enc(instr.data.subarray(2, 34));
      const hasFreezeAuth = instr.data[34];
      const freezeAuth = hasFreezeAuth ? b58enc(instr.data.subarray(35, 67)) : null;
      const mintPk     = instr.accounts[0].pubkey;
      const mintAcct   = ledger.get(mintPk);
      if (!mintAcct) throw mkErr(-32003, `Mint account not found: ${mintPk}`);
      mintAcct.data  = encodeMint(mintAuth, decimals, 0n, freezeAuth);
      mintAcct.owner = TOKEN_PROGRAM_ID;
      break;
    }
    case 1: {
      const taPk    = instr.accounts[0].pubkey;
      const mintPk  = instr.accounts[1].pubkey;
      const ownerPk = instr.accounts[2].pubkey;
      const taAcct  = ledger.get(taPk);
      if (!taAcct) throw mkErr(-32003, `Token account not found: ${taPk}`);
      taAcct.data  = encodeTA(mintPk, ownerPk, 0n, 1);
      taAcct.owner = TOKEN_PROGRAM_ID;
      break;
    }
    case 3: {
      // Transfer: accounts=[source, destination, owner]
      if (instr.data.length < 9) throw mkErr(-32003, "Transfer: data too short");
      const amount  = instr.data.readBigUInt64LE(1);
      const srcPk   = instr.accounts[0].pubkey;
      const dstPk   = instr.accounts[1].pubkey;
      const ownerPk = instr.accounts[2].pubkey;
      requireSigner(ownerPk, "token owner");
      const srcAcct = mustAcct(srcPk);
      const src = decodeTA(srcAcct.data);
      if (src.owner !== ownerPk) throw mkErr(-32003, `Transfer: owner mismatch (expected ${src.owner})`);
      if (src.amount < amount)   throw mkErr(-32003, `Transfer: insufficient balance (have ${src.amount}, need ${amount})`);
      const dstAcct = mustAcct(dstPk);
      const dst = decodeTA(dstAcct.data);
      // FIX 2: Enforce that source and destination token accounts hold the same mint.
      // Real SPL Token rejects transfers between accounts with different mints.
      if (src.mint !== dst.mint) throw mkErr(-32003, `Transfer: source mint (${src.mint}) != destination mint (${dst.mint})`);
      srcAcct.data = encodeTA(src.mint, src.owner, src.amount - amount);
      dstAcct.data = encodeTA(dst.mint, dst.owner, dst.amount + amount);
      break;
    }
    case 4: break; // Approve — simplified
    case 5: break; // Revoke — simplified
    case 6: {
      if (instr.data.length < 3) throw mkErr(-32003, "SetAuthority: too short");
      const authorityType  = instr.data[1];
      const newAuthPresent = instr.data[2];
      const newAuth = newAuthPresent ? b58enc(instr.data.subarray(3, 35)) : null;
      const acctPk  = instr.accounts[0].pubkey;
      const curAuthPk = instr.accounts[1].pubkey;
      requireSigner(curAuthPk, "current authority");
      if (authorityType === 0) {
        const mintAcct = ledger.get(acctPk);
        if (!mintAcct || mintAcct.data.length < MINT_SIZE) break;
        const mint = decodeMint(mintAcct.data);
        mintAcct.data = encodeMint(newAuth, mint.decimals, mint.supply, mint.freezeAuth);
      } else if (authorityType === 2) {
        const taAcct = ledger.get(acctPk);
        if (!taAcct || taAcct.data.length < TOKEN_ACCOUNT_SIZE) break;
        const ta = decodeTA(taAcct.data);
        taAcct.data = encodeTA(ta.mint, newAuth ?? ta.owner, ta.amount);
      }
      break;
    }
    case 7: {
      // MintTo: accounts=[mint, destination, authority]
      if (instr.data.length < 9) throw mkErr(-32003, "MintTo: data too short");
      const amount   = instr.data.readBigUInt64LE(1);
      const mintPk   = instr.accounts[0].pubkey;
      const destPk   = instr.accounts[1].pubkey;
      const authPk   = instr.accounts[2].pubkey;
      requireSigner(authPk, "mint authority");
      const mintAcct = mustAcct(mintPk);
      const mint     = decodeMint(mintAcct.data);
      if (mint.mintAuth !== authPk) throw mkErr(-32003, `MintTo: wrong authority (expected ${mint.mintAuth})`);
      const destAcct = mustAcct(destPk);
      const ta = decodeTA(destAcct.data);
      // Destination token account must be for this mint
      if (ta.mint !== mintPk) throw mkErr(-32003, `MintTo: destination account mint mismatch`);
      destAcct.data = encodeTA(ta.mint, ta.owner, ta.amount + amount);
      mintAcct.data = encodeMint(mint.mintAuth, mint.decimals, mint.supply + amount, mint.freezeAuth);
      break;
    }
    case 8: {
      // Burn: accounts=[tokenAccount, mint, owner]
      if (instr.data.length < 9) throw mkErr(-32003, "Burn: data too short");
      const amount  = instr.data.readBigUInt64LE(1);
      const taPk    = instr.accounts[0].pubkey;
      const mintPk  = instr.accounts[1].pubkey;
      const ownerPk = instr.accounts[2].pubkey;
      requireSigner(ownerPk, "token owner");
      const taAcct   = mustAcct(taPk);
      const ta       = decodeTA(taAcct.data);
      if (ta.owner !== ownerPk) throw mkErr(-32003, "Burn: owner mismatch");
      if (ta.amount < amount)   throw mkErr(-32003, `Burn: insufficient balance (have ${ta.amount})`);
      // Token account must be for the specified mint
      if (ta.mint !== mintPk) throw mkErr(-32003, `Burn: token account mint mismatch`);
      const mintAcct = mustAcct(mintPk);
      const mint     = decodeMint(mintAcct.data);
      taAcct.data   = encodeTA(ta.mint, ta.owner, ta.amount - amount);
      mintAcct.data = encodeMint(mint.mintAuth, mint.decimals, mint.supply - amount, mint.freezeAuth);
      break;
    }
    case 9: {
      const taPk    = instr.accounts[0].pubkey;
      const destPk  = instr.accounts[1].pubkey;
      const ownerPk = instr.accounts[2].pubkey;
      requireSigner(ownerPk, "close authority");
      const taAcct = mustAcct(taPk);
      const ta     = decodeTA(taAcct.data);
      if (ta.owner !== ownerPk) throw mkErr(-32003, "CloseAccount: owner mismatch");
      if (ta.amount !== 0n)     throw mkErr(-32003, "CloseAccount: non-zero token balance");
      touchAcct(destPk).lamports += taAcct.lamports;
      ledger.delete(taPk);
      break;
    }
    case 12: {
      // TransferChecked: accounts=[source, mint, destination, owner]
      if (instr.data.length < 10) throw mkErr(-32003, "TransferChecked: data too short");
      const amount   = instr.data.readBigUInt64LE(1);
      const decimals = instr.data[9];
      const srcPk    = instr.accounts[0].pubkey;
      const mintPk   = instr.accounts[1].pubkey;
      const dstPk    = instr.accounts[2].pubkey;
      const ownerPk  = instr.accounts[3].pubkey;
      requireSigner(ownerPk, "token owner");
      const mintAcct = mustAcct(mintPk);
      const mint     = decodeMint(mintAcct.data);
      if (mint.decimals !== decimals) throw mkErr(-32003, `TransferChecked: decimals mismatch (expected ${mint.decimals})`);
      const srcAcct  = mustAcct(srcPk);
      const src      = decodeTA(srcAcct.data);
      if (src.owner !== ownerPk) throw mkErr(-32003, "TransferChecked: owner mismatch");
      if (src.amount < amount)   throw mkErr(-32003, `TransferChecked: insufficient balance (have ${src.amount})`);
      // FIX 2: Both source and destination must match the explicitly supplied mint.
      if (src.mint !== mintPk) throw mkErr(-32003, `TransferChecked: source account mint mismatch`);
      const dstAcct  = mustAcct(dstPk);
      const dst      = decodeTA(dstAcct.data);
      if (dst.mint !== mintPk) throw mkErr(-32003, `TransferChecked: destination account mint mismatch`);
      srcAcct.data  = encodeTA(src.mint, src.owner, src.amount - amount);
      dstAcct.data  = encodeTA(dst.mint, dst.owner, dst.amount + amount);
      break;
    }
    case 14: {
      // MintToChecked: accounts=[mint, destination, authority]
      if (instr.data.length < 10) throw mkErr(-32003, "MintToChecked: data too short");
      const amount   = instr.data.readBigUInt64LE(1);
      const decimals = instr.data[9];
      const mintPk   = instr.accounts[0].pubkey;
      const destPk   = instr.accounts[1].pubkey;
      const authPk   = instr.accounts[2].pubkey;
      requireSigner(authPk, "mint authority");
      const mintAcct = mustAcct(mintPk);
      const mint     = decodeMint(mintAcct.data);
      if (mint.mintAuth !== authPk) throw mkErr(-32003, `MintToChecked: wrong authority`);
      if (mint.decimals !== decimals) throw mkErr(-32003, `MintToChecked: decimals mismatch`);
      const destAcct = mustAcct(destPk);
      const ta = decodeTA(destAcct.data);
      if (ta.mint !== mintPk) throw mkErr(-32003, `MintToChecked: destination account mint mismatch`);
      destAcct.data = encodeTA(ta.mint, ta.owner, ta.amount + amount);
      mintAcct.data = encodeMint(mint.mintAuth, mint.decimals, mint.supply + amount, mint.freezeAuth);
      break;
    }
    case 15: {
      // BurnChecked: accounts=[tokenAccount, mint, owner]
      if (instr.data.length < 10) throw mkErr(-32003, "BurnChecked: data too short");
      const amount   = instr.data.readBigUInt64LE(1);
      const decimals = instr.data[9];
      const taPk     = instr.accounts[0].pubkey;
      const mintPk   = instr.accounts[1].pubkey;
      const ownerPk  = instr.accounts[2].pubkey;
      requireSigner(ownerPk, "token owner");
      const mintAcct = mustAcct(mintPk);
      const mint     = decodeMint(mintAcct.data);
      if (mint.decimals !== decimals) throw mkErr(-32003, "BurnChecked: decimals mismatch");
      const taAcct   = mustAcct(taPk);
      const ta       = decodeTA(taAcct.data);
      if (ta.owner !== ownerPk) throw mkErr(-32003, "BurnChecked: owner mismatch");
      if (ta.amount < amount)   throw mkErr(-32003, `BurnChecked: insufficient balance`);
      if (ta.mint !== mintPk)   throw mkErr(-32003, `BurnChecked: token account mint mismatch`);
      taAcct.data   = encodeTA(ta.mint, ta.owner, ta.amount - amount);
      mintAcct.data = encodeMint(mint.mintAuth, mint.decimals, mint.supply - amount, mint.freezeAuth);
      break;
    }
    case 16: {
      if (instr.data.length < 33) throw mkErr(-32003, "InitializeAccount2: data too short");
      const ownerPk = b58enc(instr.data.subarray(1, 33));
      const taPk    = instr.accounts[0].pubkey;
      const mintPk  = instr.accounts[1].pubkey;
      const taAcct  = ledger.get(taPk);
      if (!taAcct) throw mkErr(-32003, `Token account not found: ${taPk}`);
      taAcct.data  = encodeTA(mintPk, ownerPk, 0n, 1);
      taAcct.owner = TOKEN_PROGRAM_ID;
      break;
    }
    case 18: {
      if (instr.data.length < 33) throw mkErr(-32003, "InitializeAccount3: data too short");
      const ownerPk = b58enc(instr.data.subarray(1, 33));
      const taPk    = instr.accounts[0].pubkey;
      const mintPk  = instr.accounts[1].pubkey;
      const taAcct  = ledger.get(taPk);
      if (!taAcct) throw mkErr(-32003, `Token account not found: ${taPk}`);
      taAcct.data  = encodeTA(mintPk, ownerPk, 0n, 1);
      taAcct.owner = TOKEN_PROGRAM_ID;
      break;
    }
    case 20: {
      if (instr.data.length < 35) throw mkErr(-32003, "InitializeMint2: data too short");
      const decimals      = instr.data[1];
      const mintAuth      = b58enc(instr.data.subarray(2, 34));
      const hasFreezeAuth = instr.data[34];
      const freezeAuth    = (hasFreezeAuth && instr.data.length >= 67) ? b58enc(instr.data.subarray(35, 67)) : null;
      const mintPk        = instr.accounts[0].pubkey;
      const mintAcct      = ledger.get(mintPk);
      if (!mintAcct) throw mkErr(-32003, `Mint account not found: ${mintPk}`);
      if (mintAcct.data.length >= MINT_SIZE) {
        const existing = decodeMint(mintAcct.data);
        if (existing.isInitialized) throw mkErr(-32003, "Mint already initialized");
      }
      mintAcct.data  = encodeMint(mintAuth, decimals, 0n, freezeAuth);
      mintAcct.owner = TOKEN_PROGRAM_ID;
      break;
    }
    default:
      throw mkErr(-32003, `Unknown SPL Token instruction: ${disc}`);
  }
}

// ── Associated Token Account Program ──────────────────────────────────────────
function execATA(instr: TxInstruction): void {
  const disc    = instr.data.length > 0 ? instr.data[0] : 0;
  const payerPk = instr.accounts[0].pubkey;
  const ataPk   = instr.accounts[1].pubkey;
  const ownerPk = instr.accounts[2].pubkey;
  const mintPk  = instr.accounts[3].pubkey;
  requireSigner(payerPk, "payer");
  const expected = deriveATA(ownerPk, mintPk);
  if (expected !== ataPk) throw mkErr(-32003, `ATA address mismatch: expected ${expected}, got ${ataPk}`);
  if (accountExists(ataPk)) {
    if (disc === 1) return;
    throw mkErr(-32003, "ATA already exists");
  }
  const rent = rentExempt(TOKEN_ACCOUNT_SIZE);
  const payerAcct = touchAcct(payerPk);
  if (payerAcct.lamports < rent) throw mkErr(-32003, `Insufficient funds for ATA rent: need ${rent}, have ${payerAcct.lamports}`);
  payerAcct.lamports -= rent;
  ledger.set(ataPk, { lamports: rent, owner: TOKEN_PROGRAM_ID, data: encodeTA(mintPk, ownerPk, 0n, 1), executable: false });
}

// ─── Full transaction execution ────────────────────────────────────────────────
function execTx(tx: ParsedTx): void {
  // FIX 1: Enforce blockhash expiration.
  // Real Solana rejects a transaction if currentSlot > lastValidBlockHeight.
  const bhInfo = blockhashRegistry.get(tx.blockhash);
  if (!bhInfo) throw mkErr(-32003, `Blockhash not found: ${tx.blockhash}`);
  if (slot > bhInfo.lastValidBlockHeight) throw mkErr(-32003, `Blockhash expired (valid through slot ${bhInfo.lastValidBlockHeight}, current slot ${slot})`);

  currentSigners = new Set(tx.signerKeys);
  for (const instr of tx.instructions) {
    const pid = instr.programId;
    if      (pid === SYSTEM_PROGRAM_ID) execSystem(instr);
    else if (pid === TOKEN_PROGRAM_ID)  execToken(instr);
    else if (pid === ATA_PROGRAM_ID)    execATA(instr);
    // else: silently skip (ComputeBudget, Memo, etc.)
  }
  slot++;
}

// ─── AccountInfo serializer ────────────────────────────────────────────────────
function serAcct(acct: Account) {
  return {
    data:       [acct.data.toString("base64"), "base64"] as [string, string],
    executable: acct.executable,
    lamports:   acct.lamports,
    owner:      acct.owner,
    rentEpoch:  0,
    space:      acct.data.length,
  };
}

function isRealAccount(acct: Account | undefined): boolean {
  if (!acct) return false;
  return acct.executable || acct.lamports > 0 || acct.data.length > 0;
}

// ─── getProgramAccounts filter helpers ────────────────────────────────────────
interface MemcmpFilter { offset: number; bytes: string; }
type Filter = { memcmp: MemcmpFilter } | { dataSize: number };

function applyFilters(acct: Account, filters: Filter[]): boolean {
  for (const f of filters) {
    if ("dataSize" in f) {
      if (acct.data.length !== f.dataSize) return false;
    } else if ("memcmp" in f) {
      const { offset, bytes } = f.memcmp;
      let cmpBytes: Buffer;
      try { cmpBytes = b58dec(bytes); } catch { return false; }
      if (offset + cmpBytes.length > acct.data.length) return false;
      for (let i = 0; i < cmpBytes.length; i++) {
        if (acct.data[offset + i] !== cmpBytes[i]) return false;
      }
    }
  }
  return true;
}

// ─── RPC dispatch ─────────────────────────────────────────────────────────────
function dispatch(method: string, params: unknown[]): unknown {
  switch (method) {
    case "getVersion":
      return { "solana-core": "1.18.26", "feature-set": 3580551090 };
    case "getSlot":
      return slot;
    case "getBlockHeight":
      return slot;
    case "getHealth":
      return "ok";
    case "getIdentity":
      return { identity: b58enc(nacl.randomBytes(32)) };
    case "getClusterNodes":
      return [];
    case "getVoteAccounts":
      return { current: [], delinquent: [] };
    case "getEpochInfo":
      return { epoch: 0, slotIndex: slot, slotsInEpoch: 432000, absoluteSlot: slot, blockHeight: slot, transactionCount: confirmedTxs.size };
    case "getEpochSchedule":
      return { slotsPerEpoch: 432000, leaderScheduleSlotOffset: 432000, warmup: false, firstNormalEpoch: 0, firstNormalSlot: 0 };
    case "getInflationRate":
      return { total: 0.08, validator: 0.08, foundation: 0, epoch: 0 };
    case "getInflationGovernor":
      return { initial: 0.08, terminal: 0.015, taper: 0.15, foundation: 0, foundationTerm: 0 };
    case "getSupply":
      return { context: { slot }, value: { total: 0, circulating: 0, nonCirculating: 0, nonCirculatingAccounts: [] } };
    case "minimumLedgerSlot":
    case "getFirstAvailableBlock":
      return 0;
    case "getMaxRetransmitSlot":
    case "getMaxShredInsertSlot":
      return slot;

    // ── Blockhash ─────────────────────────────────────────────────────────────
    case "getLatestBlockhash": {
      const hash = freshBlockhash();
      return { context: { slot }, value: { blockhash: hash, lastValidBlockHeight: slot + 300 } };
    }
    case "getRecentBlockhash": {
      const hash = freshBlockhash();
      return {
        context: { slot },
        value: { blockhash: hash, feeCalculator: { lamportsPerSignature: 5000 } },
      };
    }
    case "isBlockhashValid": {
      const hash = params[0] as string;
      const bhInfo = blockhashRegistry.get(hash);
      const valid = !!bhInfo && slot <= bhInfo.lastValidBlockHeight;
      return { context: { slot }, value: valid };
    }
    case "getFeeForMessage":
      return { context: { slot }, value: 5000 };

    // ── Accounts ──────────────────────────────────────────────────────────────
    case "getBalance": {
      const pk   = params[0] as string;
      const acct = ledger.get(pk);
      return { context: { slot }, value: acct ? acct.lamports : 0 };
    }
    case "getAccountInfo": {
      const pk   = params[0] as string;
      const acct = ledger.get(pk);
      if (!isRealAccount(acct)) return { context: { slot }, value: null };
      return { context: { slot }, value: serAcct(acct!) };
    }
    case "getMultipleAccounts": {
      const pks   = params[0] as string[];
      const value = pks.map(pk => {
        const a = ledger.get(pk);
        if (!isRealAccount(a)) return null;
        return serAcct(a!);
      });
      return { context: { slot }, value };
    }
    case "getProgramAccounts": {
      const programId = params[0] as string;
      const opts = (params[1] ?? {}) as Record<string, unknown>;
      const filters: Filter[] = Array.isArray(opts.filters) ? opts.filters as Filter[] : [];
      const result: unknown[] = [];
      for (const [pk, acct] of ledger) {
        if (acct.owner !== programId) continue;
        if (!isRealAccount(acct)) continue;
        if (filters.length > 0 && !applyFilters(acct, filters)) continue;
        result.push({ pubkey: pk, account: serAcct(acct) });
      }
      return result;
    }
    case "getMinimumBalanceForRentExemption": {
      const size = typeof params[0] === "number" ? params[0] : 0;
      return rentExempt(size);
    }

    // ── Token ─────────────────────────────────────────────────────────────────
    case "getTokenAccountBalance": {
      const pk   = params[0] as string;
      const acct = ledger.get(pk);
      if (!acct || acct.data.length < TOKEN_ACCOUNT_SIZE) throw mkErr(-32602, "Account not found or not a token account");
      const ta = decodeTA(acct.data);
      const mA = ledger.get(ta.mint);
      const decimals = (mA && mA.data.length >= MINT_SIZE) ? decodeMint(mA.data).decimals : 0;
      const uiAmt = Number(ta.amount) / Math.pow(10, decimals);
      return { context: { slot }, value: { amount: ta.amount.toString(), decimals, uiAmount: uiAmt, uiAmountString: uiAmt.toString() } };
    }
    case "getTokenSupply": {
      const pk   = params[0] as string;
      const acct = ledger.get(pk);
      if (!acct || acct.data.length < MINT_SIZE) throw mkErr(-32602, "Mint not found");
      const mint  = decodeMint(acct.data);
      const uiAmt = Number(mint.supply) / Math.pow(10, mint.decimals);
      return { context: { slot }, value: { amount: mint.supply.toString(), decimals: mint.decimals, uiAmount: uiAmt, uiAmountString: uiAmt.toString() } };
    }
    case "getTokenAccountsByOwner": {
      const ownerPk = params[0] as string;
      const filter  = (params[1] ?? {}) as Record<string, string>;
      const results: unknown[] = [];
      for (const [pk, acct] of ledger) {
        if (acct.owner !== TOKEN_PROGRAM_ID) continue;
        if (acct.data.length < TOKEN_ACCOUNT_SIZE) continue;
        let ta: ReturnType<typeof decodeTA>;
        try { ta = decodeTA(acct.data); } catch { continue; }
        if (ta.owner !== ownerPk) continue;
        if (filter.mint && ta.mint !== filter.mint) continue;
        if (filter.programId && filter.programId !== TOKEN_PROGRAM_ID) continue;
        results.push({ pubkey: pk, account: serAcct(acct) });
      }
      return { context: { slot }, value: results };
    }
    case "getTokenLargestAccounts": {
      const mintPk = params[0] as string;
      const mA     = ledger.get(mintPk);
      const decimals = (mA && mA.data.length >= MINT_SIZE) ? decodeMint(mA.data).decimals : 0;
      const results: { address: string; amount: string; decimals: number; uiAmount: number; uiAmountString: string }[] = [];
      for (const [pk, acct] of ledger) {
        if (acct.owner !== TOKEN_PROGRAM_ID || acct.data.length < TOKEN_ACCOUNT_SIZE) continue;
        try {
          const ta = decodeTA(acct.data);
          if (ta.mint !== mintPk) continue;
          const uiAmt = Number(ta.amount) / Math.pow(10, decimals);
          results.push({ address: pk, amount: ta.amount.toString(), decimals, uiAmount: uiAmt, uiAmountString: uiAmt.toString() });
        } catch { continue; }
      }
      results.sort((a, b) => { const diff = BigInt(b.amount) - BigInt(a.amount); return diff > 0n ? 1 : diff < 0n ? -1 : 0; });
      return { context: { slot }, value: results.slice(0, 20) };
    }

    // ── Transactions ──────────────────────────────────────────────────────────
    case "requestAirdrop": {
      const pk       = params[0] as string;
      const lamports = Number(params[1]);
      if (isNaN(lamports) || lamports <= 0) throw mkErr(-32602, "Invalid lamport amount");
      touchAcct(pk).lamports += lamports;
      const sig = fakeSig();
      confirmedTxs.set(sig, { slot, err: null });
      slot++;
      return sig;
    }
    case "sendTransaction": {
      const encoded = params[0] as string;
      let raw: Buffer;
      try { raw = Buffer.from(encoded, "base64"); } catch { throw mkErr(-32600, "Invalid base64 encoding"); }
      let tx: ParsedTx;
      try { tx = parseTx(raw); } catch (e) { throw mkErr(-32003, `Transaction parse error: ${(e as Error).message}`); }
      try { verifySigs(tx); } catch (e) {
        if ((e as { code?: number }).code) throw e;
        throw mkErr(-32003, `Signature verification failed: ${(e as Error).message}`);
      }
      const snapshot = new Map<string, Account>();
      for (const [k, v] of ledger) snapshot.set(k, { ...v, data: Buffer.from(v.data) });
      try {
        execTx(tx);
      } catch (e) {
        ledger.clear();
        for (const [k, v] of snapshot) ledger.set(k, v);
        if ((e as { code?: number }).code) throw e;
        throw mkErr(-32003, `Transaction execution failed: ${(e as Error).message}`);
      }
      const sig = b58enc(tx.signatures[0]);
      confirmedTxs.set(sig, { slot, err: null });
      return sig;
    }
    case "simulateTransaction": {
      const encoded = params[0] as string;
      let raw: Buffer;
      try { raw = Buffer.from(encoded, "base64"); } catch { throw mkErr(-32600, "Invalid base64"); }
      let tx: ParsedTx;
      try { tx = parseTx(raw); } catch (e) { throw mkErr(-32003, `Parse: ${(e as Error).message}`); }
      const snapshot = new Map<string, Account>();
      for (const [k, v] of ledger) snapshot.set(k, { ...v, data: Buffer.from(v.data) });
      let err: string | null = null;
      try {
        currentSigners = new Set(tx.signerKeys);
        for (const instr of tx.instructions) {
          const pid = instr.programId;
          if      (pid === SYSTEM_PROGRAM_ID) execSystem(instr);
          else if (pid === TOKEN_PROGRAM_ID)  execToken(instr);
          else if (pid === ATA_PROGRAM_ID)    execATA(instr);
        }
      } catch (e) { err = (e as Error).message ?? String(e); }
      ledger.clear();
      for (const [k, v] of snapshot) ledger.set(k, v);
      return { context: { slot }, value: { err, logs: [], accounts: null, unitsConsumed: 200000, returnData: null } };
    }
    case "getSignatureStatuses": {
      const sigs  = (params[0] as string[]) ?? [];
      const value = sigs.map(sig => {
        const info = confirmedTxs.get(sig);
        if (!info) return null;
        return { slot: info.slot, confirmations: null, err: info.err, confirmationStatus: "finalized" };
      });
      return { context: { slot }, value };
    }
    case "getSignatureStatus": {
      const sig  = params[0] as string;
      const info = confirmedTxs.get(sig);
      if (!info) return { context: { slot }, value: null };
      return { context: { slot }, value: { slot: info.slot, confirmations: null, err: info.err, confirmationStatus: "finalized" } };
    }
    case "getTransaction": {
      const sig = params[0] as string;
      if (!confirmedTxs.has(sig)) return null;
      return { slot, blockTime: Math.floor(Date.now() / 1000), meta: { err: null, fee: 5000, preBalances: [], postBalances: [], logMessages: [] } };
    }
    case "getSignaturesForAddress":
    case "getConfirmedSignaturesForAddress":
    case "getConfirmedSignaturesForAddress2":
    case "getConfirmedTransaction":
      return null;
    case "getBlock":
    case "getConfirmedBlock":
      return null;
    case "getBlocks":
    case "getConfirmedBlocks":
      return [];
    case "getBlockTime":
      return Math.floor(Date.now() / 1000);
    case "getBlockCommitment":
      return { commitment: null, totalStake: 0 };
    case "getStakeActivation":
      return { state: "active", active: 0, inactive: 0 };
    default:
      throw mkErr(-32601, `Method not found: ${method}`);
  }
}

// ─── Express server ────────────────────────────────────────────────────────────
const app = express();
app.use(express.json({ limit: "50mb" }));

type RpcBody = { jsonrpc?: string; id?: unknown; method?: string; params?: unknown[]; };

function processOne(body: RpcBody) {
  const { jsonrpc, id, method, params } = body ?? {};
  if (!method || jsonrpc !== "2.0") {
    return { jsonrpc: "2.0", id: id ?? null, error: { code: -32600, message: "Invalid request: missing method or invalid jsonrpc version" } };
  }
  try {
    return { jsonrpc: "2.0", id, result: dispatch(method, params ?? []) };
  } catch (e: unknown) {
    const err = e as { code?: number; message?: string };
    if (typeof err?.code === "number") return { jsonrpc: "2.0", id, error: { code: err.code, message: err.message } };
    console.error(`[${method}] Unhandled error:`, e);
    return { jsonrpc: "2.0", id, error: { code: -32603, message: String(e) } };
  }
}

app.post("/", (req: Request, res: Response) => {
  if (Array.isArray(req.body)) res.json(req.body.map((item: RpcBody) => processOne(item)));
  else res.json(processOne(req.body as RpcBody));
});

app.get("/health", (_req, res) => res.send("ok"));

const PORT = 3000;
app.listen(PORT, () => {
  console.log(`Mini Solana Validator listening on port ${PORT}`);
  console.log(`Slot: ${slot}, Pre-generated blockhashes: ${blockhashRegistry.size}`);
});
