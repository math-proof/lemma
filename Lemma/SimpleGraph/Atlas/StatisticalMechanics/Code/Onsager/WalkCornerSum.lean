import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WalkCornerSum
open StatMech StatMech.Onsager StatMech.Onsager.WalkCornerSum


/--
[cornerWeight_zero_of_notMem_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCornerSum.lean)
-/
@[path]
private lemma cornerWeight_zero_of_notMem_image_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hnv : ∀ k : Fin n, pos d k ≠ (vx, vy)) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (vx, vy)) = 0 := by
-- proof
  apply StatMech.Onsager.WalkCornerSum.cornerWeight_zero_of_notMem_image d hclosed vx vy hnv

/--
[cornerDiff_interior_eq_walk_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCornerSum.lean)
-/
@[path]
private lemma cornerDiff_interior_eq_walk_sum_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  cornerDiff (interiorCells d hclosed) = ∑ k : Fin n, cornerWeight (cornerCount (interiorCells d hclosed) (pos d k)) := by
-- proof
  apply StatMech.Onsager.WalkCornerSum.cornerDiff_interior_eq_walk_sum d hclosed hsimple


-- created on 2026-10-23
