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


def rows(obs, tables, w_in, t):
    """relu(W_t x) for every row of table t, real or not: (B, rows_t, E). Padding rows are zero in the
    environment, and with no biases they give zero here."""
    off, nrows, width = tables[t]
    x = obs[:, off:off + nrows * width].reshape(obs.shape[0], nrows, width)
    return torch.relu(x @ w_in[t].T)


def pointer_logits(obs, tables, w_in, h, ptr, kind_t, spot_t, link_t, act_spot, act_link, act_size,
                   res_t=None, act_bank=None, E=None):
    """The pointer decoder's added scores, as a (B, act_size) tensor that is zero outside spot, link (and bank)
    actions. `ptr` has 2E rows, or 4E with the bank part (pass res_t and act_bank, and E).

    q = h @ ptr.T, split into q_spot and q_link (E each).
    logit(spot v, kind k) = sum_e q_spot[e] * r_spot[v][e] * r_kind[1 + k][e]    at act_spot + k * spots + v
    logit(link j)         = sum_e q_link[e] * r_link[j][e] * r_kind[0][e]        at act_link + j
    logit(bank i -> j)    = q_give . r_res[i] + q_get . r_res[j]                  at act_bank + i * res + j
    """
    E = E or ptr.shape[0] // 2
    q = h @ ptr.T
    qs, ql = q[:, :E], q[:, E:2 * E]
    rk = rows(obs, tables, w_in, kind_t)            # (B, 1 + kinds, E)
    rs = rows(obs, tables, w_in, spot_t)            # (B, spots, E)
    rl = rows(obs, tables, w_in, link_t)            # (B, links, E)
    spot = torch.einsum("be,bve,bke->bkv", qs, rs, rk[:, 1:])     # (B, kinds, spots)
    link = torch.einsum("be,bje,be->bj", ql, rl, rk[:, 0])        # (B, links)
    B = obs.shape[0]
    out = torch.zeros(B, act_size, dtype=obs.dtype)
    out = out.index_put((torch.arange(B)[:, None], act_spot + torch.arange(spot[0].numel())[None, :]),
                        spot.reshape(B, -1))
    out = out.index_put((torch.arange(B)[:, None], act_link + torch.arange(link.shape[1])[None, :]), link)
    if ptr.shape[0] == 4 * E:
        rr = rows(obs, tables, w_in, res_t)                       # (B, res, E)
        give = (rr * q[:, None, 2 * E:3 * E]).sum(2)              # (B, res)
        get = (rr * q[:, None, 3 * E:]).sum(2)
        bank = (give[:, :, None] + get[:, None, :]).reshape(B, -1)
        out = out.index_put((torch.arange(B)[:, None], act_bank + torch.arange(bank.shape[1])[None, :]), bank)
    return out
