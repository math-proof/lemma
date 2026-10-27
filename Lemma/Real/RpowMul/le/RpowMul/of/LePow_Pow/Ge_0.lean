import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_rpow_of_nat_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (a b ra rb : ℕ)
  (c : ℝ)
-- given
  (hc : 0 ≤ c)
  (hab : a ^ ra ≤ b ^ rb) :
-- imply
  Real.rpow a (c * ra) ≤ Real.rpow b (c * rb) := by
-- proof
  have habR : ((a ^ ra : ℕ) : ℝ) ≤ (b ^ rb : ℕ) := by exact_mod_cast hab
  calc
    _ = Real.rpow a ((ra : ℝ) * c) := by ring_nf
    _ = Real.rpow (Real.rpow a (ra : ℝ)) c :=
      Real.rpow_mul (Nat.cast_nonneg _) _ _
    _ = Real.rpow (a ^ ra : ℕ) c := by
      congr 1
      exact (Real.rpow_natCast (a : ℝ) ra).trans (by norm_cast)
    _ ≤ Real.rpow (b ^ rb : ℕ) c :=
      Real.rpow_le_rpow (by positivity) habR hc
    _ = Real.rpow (Real.rpow b (rb : ℝ)) c := by
      congr 1
      exact ((Real.rpow_natCast (b : ℝ) rb).trans (by norm_cast)).symm
    _ = Real.rpow b ((rb : ℝ) * c) :=
      (Real.rpow_mul (Nat.cast_nonneg _) _ _).symm
    _ = Real.rpow b (c * rb) := by ring_nf


-- created on 2026-10-21
