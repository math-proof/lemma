import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_denProduct_le_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (Q η : ℝ)
-- given
  (hQ : 0 ≤ Q)
  (hupper : ∀ h, ((q h).den : ℝ) ^ r h ≤ Real.rpow Q (1 + η)) :
-- imply
  (rothDenProduct q r : ℝ) ≤ Real.rpow Q ((m : ℝ) * (1 + η)) := by
-- proof
  unfold rothDenProduct
  push_cast
  calc
    _ ≤ ∏ _ : Fin m, Real.rpow Q (1 + η) := by
      gcongr with h
      exact hupper h
    _ = (Real.rpow Q (1 + η)) ^ m := by simp
    _ = Real.rpow (Real.rpow Q (1 + η)) (m : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = Real.rpow Q ((1 + η) * (m : ℝ)) :=
      (Real.rpow_mul hQ _ _).symm
    _ = Real.rpow Q ((m : ℝ) * (1 + η)) := by ring_nf


-- created on 2026-10-21
