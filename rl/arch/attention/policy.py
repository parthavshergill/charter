"""rl/eval's loader for `puffer-attention` checkpoints: the attention encoder (attention_np.py), then the harness's
MinGRU and linear decoder (rl/reference/policy.py)."""
try:
    from .attention_np import load
except ImportError:  # run from this folder
    from attention_np import load
from reference.policy import FlatNet


class AttentionNet(FlatNet):
    def forward(self, obs, state):
        from reference.policy import mingru_step
        x = self.encoder(obs)
        out = []
        for W, s in zip(self.grus, state):
            x, s2 = mingru_step(W, x, s)
            out.append(s2)
        y = self.decoder @ x
        return y[:-1], y[-1], out


def load_policy(path, meta):
    enc, dec, grus = load(path, meta)
    return AttentionNet(enc, dec, grus, meta["act_size"])
