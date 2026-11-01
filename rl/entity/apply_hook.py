"""Add the entity encoder to a PufferLib checkout at the pinned commit: the include and the branch in
create_custom_encoder that PUFFER_FINDINGS.md describes (src/ocean.cu). Safe to run twice.

Usage: python rl/entity/apply_hook.py <pufferlib dir>
Then build with NVCC_EXTRA="-DPUFFER_CHARTER_ENTITY -I<charter>/rl/entity -I<dir holding charter_entity_layout.h>".
"""
import sys
from pathlib import Path

INCLUDE = '#ifdef PUFFER_CHARTER_ENTITY\n#include "charter_entity.cu"\n#endif\n'
BRANCH = '#elif defined(PUFFER_CHARTER_ENTITY)\n    create_charter_entity_encoder(enc);\n'


def patch(text):
    if "PUFFER_CHARTER_ENTITY" in text:
        return text
    anchor = "// Override encoder vtable when this env has a custom net."
    assert text.count(anchor) == 1, "src/ocean.cu is not the pinned version"
    text = text.replace(anchor, INCLUDE + "\n" + anchor)
    fallback = "#else\n    (void)enc;\n#endif\n}\n\nstatic void create_custom_decoder"
    assert text.count(fallback) == 1, "src/ocean.cu is not the pinned version"
    return text.replace(fallback, BRANCH + fallback)


if __name__ == "__main__":
    path = Path(sys.argv[1]) / "src" / "ocean.cu"
    path.write_text(patch(path.read_text()))
    print(f"patched {path}")
