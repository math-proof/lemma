import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothCentered_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hr : ∀ h, 0 < r h)
  (j : RothBox r)
  (h : Fin m) :
-- imply
  rothCentered r j h ^ 2 ≤ (1 : ℝ) / 4 := by
-- proof
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  have hx0 : (0 : ℝ) ≤ (j h : ℝ) / r h := by positivity
  have hx1 : (j h : ℝ) / r h ≤ 1 := by
    exact (div_le_one hrR).2 (by exact_mod_cast hjle)
  have hleft : 0 ≤ rothCentered r j h + 1 / 2 := by
    unfold rothCentered
    linarith
  have hright : 0 ≤ 1 / 2 - rothCentered r j h := by
    unfold rothCentered
    linarith
  have hprod := mul_nonneg hleft hright
  nlinarith


-- created on 2026-10-21
