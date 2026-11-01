"""Eval's entry point for `puffer-entity` checkpoints (rl/reference/policy.py `custom_loader`)."""
from entity.entity_numpy import load_entity


def load_policy(path, meta):
    """The entity policy at `path`. `entity_dim` defaults to 32, the encoder's built-in size."""
    return load_entity(path, dict({"entity_dim": 32}, **meta))
