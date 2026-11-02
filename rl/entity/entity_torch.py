"""The entity encoder in PyTorch: the reference the CUDA encoder must match.

For each table, one small layer is shared by all its rows: h = relu(W_t x).
The rows are averaged, counting only real rows (column 0 is 1). A table with
no real rows gives zeros. The averages of all tables are joined and one more
layer maps them to the hidden size: out = W_out pooled. No biases: column 0
is 1 on every real row, so it acts as one.
"""
import torch

def encode(obs, tables, w_in, w_out, resid=None):
    """obs: (B, obs_size). tables: list of (offset, rows, width).
    w_in[t]: (E, width_t). w_out: (H, len(tables) * E). resid: None, or (gain, bias, W_r1, W_r2) for the
    residual block (charter_entity.cu, CE_RESID): out = o0 + W_r2 relu(W_r1 LayerNorm(o0)), o0 = W_out pooled."""
    B = obs.shape[0]
    pooled = []
    for (off, rows, width), w in zip(tables, w_in):
        x = obs[:, off:off + rows * width].reshape(B, rows, width)
        real = (x[:, :, 0] > 0.5).to(obs.dtype)                # (B, rows)
        h = torch.relu(x @ w.T)                                 # (B, rows, E)
        count = real.sum(1, keepdim=True).clamp(min=1.0)        # (B, 1)
        pooled.append((h * real[:, :, None]).sum(1) / count)    # (B, E)
    o0 = torch.cat(pooled, 1) @ w_out.T                         # (B, H)
    if resid is None:
        return o0
    g, b, w1, w2 = resid
    z = torch.nn.functional.layer_norm(o0, (o0.shape[1],), g.reshape(-1), b.reshape(-1), eps=1e-5)
    return o0 + torch.relu(z @ w1.T) @ w2.T


def rows(obs, tables, w_in, t):
    """relu(W_t x) for every row of table t, real or not: (B, rows_t, E). Padding rows are zero in the
    environment, and with no biases they give zero here."""
    off, nrows, width = tables[t]
    x = obs[:, off:off + nrows * width].reshape(obs.shape[0], nrows, width)
    return torch.relu(x @ w_in[t].T)


def pointer_logits(obs, tables, w_in, h, ptr, place_t, res_t, act_place, act_bank, act_size, E=None):
    """The pointer decoder's added scores (layout 2), as a (B, act_size) tensor, zero outside placement and bank
    actions. ptr is (3E, H): q = h @ ptr.T is split into q_place, q_give, q_get (E each).

    logit(place p)     = q_place . r_places[p]                     at act_place + p
    logit(bank i -> j) = q_give . r_res[i] + q_get . r_res[j]      at act_bank + i * resources + j
    """
    E = E or ptr.shape[0] // 3   # pass E when ptr also has the move block (4E rows)
    q = h @ ptr[:3 * E].T
    B = obs.shape[0]
    rp = rows(obs, tables, w_in, place_t)                         # (B, places, E)
    rr = rows(obs, tables, w_in, res_t)                           # (B, res, E)
    place = (rp * q[:, None, :E]).sum(2)
    give = (rr * q[:, None, E:2 * E]).sum(2)
    get = (rr * q[:, None, 2 * E:]).sum(2)
    bank = (give[:, :, None] + get[:, None, :]).reshape(B, -1)
    out = torch.zeros(B, act_size, dtype=obs.dtype)
    ar = torch.arange(B)[:, None]
    out = out.index_put((ar, act_place + torch.arange(place.shape[1])[None, :]), place)
    out = out.index_put((ar, act_bank + torch.arange(bank.shape[1])[None, :]), bank)
    return out


def strip_moves(obs, tables, moves_t, act_col):
    """The moves table's action column routes each row's score; it is not a feature. Returns the observation with
    that column set to 0 (what the encoder sees), each row's action number (B, rows) and whether the row is real."""
    off, nrows, width = tables[moves_t]
    x = obs[:, off:off + nrows * width].reshape(obs.shape[0], nrows, width)
    acts = torch.round(x[:, :, act_col]).long()
    real = x[:, :, 0] > 0.5
    obs2 = obs.clone()
    cols = off + torch.arange(nrows) * width + act_col
    obs2[:, cols] = 0
    return obs2, acts, real


def moves_logits(obs, tables, w_in, h, ptr, moves_t, acts, real, act_size, E):
    """logit[action of row m] += q_move . r_moves[m] for real rows, q_move = rows 3E..4E of ptr times h. `obs` is the
    stripped observation."""
    q = h @ ptr[3 * E:4 * E].T                                         # (B, E)
    rm = rows(obs, tables, w_in, moves_t)                         # (B, rows, E)
    score = (rm * q[:, None, :]).sum(2) * real.to(obs.dtype)      # (B, rows)
    out = torch.zeros(obs.shape[0], act_size, dtype=obs.dtype)
    a = acts.clamp(0, act_size - 1)
    return out.scatter_add(1, a, score)
