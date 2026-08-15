#!/usr/bin/env python3
"""Differential Unicorn harness for the Caliper RV64 test lowering.

For every vector in tests/vectors/*.json (produced by
`lake env lean --run CaliperTest/Export.lean`):

* map the code at its code_base and the buffer arena at its arena_base,
* preload buffers (length slot + data) and initial registers,
* execute on Unicorn (RISC-V 64) until the final EBREAK, counting executed
  instructions with a per-instruction hook,
* assert every expected register and buffer matches the values the Caliper
  reference interpreter predicted,
* report per program: caliper_steps, rv64 instructions, and the lowering
  constant c = rv64 / caliper.

Exits nonzero on any mismatch. Run via uv only:

    cd tests && uv sync && uv run python run_unicorn.py
"""

import glob
import json
import os
import struct
import sys

from unicorn import Uc, UC_ARCH_RISCV, UC_MODE_RISCV64, UC_HOOK_CODE
from unicorn import riscv_const

PAGE = 0x1000
MAX_INSNS = 50_000_000


def align_down(a):
    return a & ~(PAGE - 1)


def align_up(a):
    return (a + PAGE - 1) & ~(PAGE - 1)


def xreg(i):
    return getattr(riscv_const, f"UC_RISCV_REG_X{i}")


def run_vector(vec):
    """Returns (instruction_count, list_of_mismatch_strings)."""
    uc = Uc(UC_ARCH_RISCV, UC_MODE_RISCV64)

    code = b"".join(struct.pack("<I", int(w, 16)) for w in vec["code_hex"])
    code_base = vec["code_base"]
    uc.mem_map(align_down(code_base), align_up(code_base + len(code)) - align_down(code_base))
    uc.mem_write(code_base, code)

    arena_base, arena_end = vec["arena_base"], vec["arena_end"]
    if arena_end > arena_base:
        uc.mem_map(align_down(arena_base), align_up(arena_end) - align_down(arena_base))

    for addr, words in vec["initial_mem"]:
        uc.mem_write(addr, b"".join(struct.pack("<Q", w) for w in words))

    for reg, val in vec["initial_regs"]:
        uc.reg_write(xreg(reg), val)

    count = [0]

    def on_insn(uc_, addr, size, _):
        count[0] += 1
        if count[0] > MAX_INSNS:
            uc_.emu_stop()

    uc.hook_add(UC_HOOK_CODE, on_insn)

    ebreak_addr = code_base + len(code) - 4
    uc.emu_start(code_base, ebreak_addr)

    errors = []
    if count[0] > MAX_INSNS:
        errors.append("instruction budget exhausted (runaway program)")

    for reg, want in vec["expected_regs"]:
        got = uc.reg_read(xreg(reg))
        if got != want:
            errors.append(f"reg x{reg}: got {got:#x}, want {want:#x}")

    for len_addr, want_len, want_words in vec["expected_bufs"]:
        (got_len,) = struct.unpack("<Q", uc.mem_read(len_addr, 8))
        if got_len != want_len:
            errors.append(f"buf@{len_addr:#x} length: got {got_len}, want {want_len}")
        else:
            data = uc.mem_read(len_addr + 8, 8 * want_len)
            got_words = list(struct.unpack(f"<{want_len}Q", data)) if want_len else []
            if got_words != want_words:
                errors.append(
                    f"buf@{len_addr:#x} contents: got {got_words}, want {want_words}"
                )

    return count[0], errors


def main():
    vec_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "vectors")
    paths = sorted(glob.glob(os.path.join(vec_dir, "*.json")))
    if not paths:
        print(f"no vectors found in {vec_dir} — run the exporter first:", file=sys.stderr)
        print("  lake env lean --run CaliperTest/Export.lean", file=sys.stderr)
        return 2

    print(f"{'program':<22} {'caliper':>8} {'rv64':>8} {'c':>6}  result")
    print("-" * 58)
    failed = False
    for path in paths:
        with open(path) as f:
            vec = json.load(f)
        name = vec["name"]
        try:
            insns, errors = run_vector(vec)
        except Exception as e:  # emulator faults are test failures too
            print(f"{name:<22} {'-':>8} {'-':>8} {'-':>6}  ERROR: {e}")
            failed = True
            continue
        steps = vec["caliper_steps"]
        c = insns / steps if steps else float("inf")
        status = "ok" if not errors else "FAIL"
        print(f"{name:<22} {steps:>8} {insns:>8} {c:>6.2f}  {status}")
        for e in errors:
            print(f"    {e}")
            failed = True

    if failed:
        print("\nFAILED: differential mismatches above", file=sys.stderr)
        return 1
    print("\nall vectors match the reference interpreter")
    return 0


if __name__ == "__main__":
    sys.exit(main())
