"""The entity encoder in PyTorch: the reference the CUDA encoder must match.

For each table, one small layer is shared by all its rows: h = relu(W_t x).
The rows are averaged, counting only real rows (column 0 is 1). A table with
no real rows gives zeros. The averages of all tables are joined and one more
layer maps them to the hidden size: out = W_out pooled. No biases: column 0
is 1 on every real row, so it acts as one.
"""
import torch

def encode(obs, tables, w_in, w_out):
    """obs: (B, obs_size). tables: list of (offset, rows, width).
    w_in[t]: (E, width_t). w_out: (H, len(tables) * E)."""
    B = obs.shape[0]
    pooled = []
    for (off, rows, width), w in zip(tables, w_in):
        x = obs[:, off:off + rows * width].reshape(B, rows, width)
        real = (x[:, :, 0] > 0.5).to(obs.dtype)                # (B, rows)
        h = torch.relu(x @ w.T)                                 # (B, rows, E)
        count = real.sum(1, keepdim=True).clamp(min=1.0)        # (B, 1)
        pooled.append((h * real[:, :, None]).sum(1) / count)    # (B, E)
    return torch.cat(pooled, 1) @ w_out.T                       # (B, H)
