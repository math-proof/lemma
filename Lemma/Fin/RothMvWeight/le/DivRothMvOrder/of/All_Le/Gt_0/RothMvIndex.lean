import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_le_order_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m b : ℕ}
  (r : Fin m → ℕ)
-- given
  (hb : 0 < b)
  (hbr : ∀ h, b ≤ r h)
  (i : RothMvIndex m) :
-- imply
  rothMvWeight r i ≤ (rothMvOrder i : ℝ) / b := by
-- proof
  unfold rothMvWeight rothMvOrder
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
  ·
    exact_mod_cast hb
  ·
    exact_mod_cast hbr h


-- created on 2026-10-21
