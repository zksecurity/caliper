import Caliper.Triple

/-!
# Corpus helpers

Small `BitVec` facts shared by the corpus proofs: the same wrap-around and
comparison-flag lemmas the examples use. `Caliper/Examples.lean` keeps its copies
`private`; the corpus needs them across files, so they live here.
-/

namespace Caliper.Corpus

variable {w : ℕ}

/-- Incrementing an index below a bound `n < 2 ^ w` does not wrap. -/
theorem toNat_add_ofNat_one {x : BitVec w} {n : ℕ}
    (hx : x.toNat < n) (hn : n < 2 ^ w) : (x + BitVec.ofNat w 1).toNat = x.toNat + 1 := by
  have h2 : 1 < 2 ^ w := by omega
  have h1 : (BitVec.ofNat w 1).toNat = 1 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt h2
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- A comparison flag `if c then 1 else 0` that is nonzero certifies `c`. -/
theorem cond_of_flag_ne {c : Prop} [Decidable c] {f : BitVec w}
    (hf : f = if c then 1 else 0) (hnz : f ≠ 0) : c := by
  by_cases hc : c
  · exact hc
  · rw [if_neg hc] at hf
    exact absurd hf hnz

/-- A zero comparison flag refutes `c`, provided the word size can distinguish 1
from 0 (`1 < 2 ^ w`), which each call site derives from its own bounds. -/
theorem not_cond_of_flag_zero {c : Prop} [Decidable c]
    (h2 : 1 < 2 ^ w) (hf : (if c then (1 : BitVec w) else 0) = 0) : ¬ c := by
  intro hc
  rw [if_pos hc] at hf
  have h := congrArg BitVec.toNat hf
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h
  rw [Nat.mod_eq_of_lt h2, Nat.zero_mod] at h
  exact one_ne_zero h

/-- A word with nonzero value has nonzero `toNat`. -/
theorem toNat_ne_zero {x : BitVec w} (hx : x ≠ 0) : x.toNat ≠ 0 := by
  intro h0
  exact hx (by apply BitVec.eq_of_toNat_eq; simp [h0])

end Caliper.Corpus
