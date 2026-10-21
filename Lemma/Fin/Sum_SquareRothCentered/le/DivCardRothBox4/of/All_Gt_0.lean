import Mathlib
import Lemma.Fin.SquareRothCentered.le.Div1'4.of.RothBox.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothCentered_sq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
-- given
  (hr : ∀ h, 0 < r h)
  (h : Fin m) :
-- imply
  ∑ j : RothBox r, rothCentered r j h ^ 2 ≤
    (Fintype.card (RothBox r) : ℝ) / 4 :=
-- proof
  calc
    _ ≤ ∑ _ : RothBox r, (1 : ℝ) / 4 := by
      gcongr with j
      apply SquareRothCentered.le.Div1'4.of.RothBox.All_Gt_0 hr
    _ = (Fintype.card (RothBox r) : ℝ) / 4 := by
      simp [div_eq_mul_inv]


-- created on 2026-10-21
