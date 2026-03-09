import express from "express";

const app = express();
app.use(express.json());

// TODO: Implement your mini Solana validator here
// Handle JSON-RPC 2.0 requests at POST /

app.post("/", (req, res) => {
  const { jsonrpc, id, method, params } = req.body;
  // Implement RPC methods here
  res.json({ jsonrpc: "2.0", id, error: { code: -32601, message: "Method not found" } });
});

const PORT = 3000;
app.listen(PORT, () => {
  console.log(`Mini Solana Validator running on port ${PORT}`);
});
