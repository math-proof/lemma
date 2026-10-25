import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBridge
open StatMech StatMech.Onsager StatMech.Onsager.WalkCellBridge


/--
[cornerCount_interior_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBridge.lean)
-/
@[path]
private lemma cornerCount_interior_eq_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (cornerCount (interiorCells d hclosed) (vx, vy) : ℤ) = (if rayParity d vx vy = 1 then (1 : ℤ) else 0) + (if rayParity d (vx - 1) vy = 1 then 1 else 0) + (if rayParity d vx (vy - 1) = 1 then 1 else 0) + (if rayParity d (vx - 1) (vy - 1) = 1 then 1 else 0) := by
-- proof
  apply StatMech.Onsager.WalkCellBridge.cornerCount_interior_eq d hclosed vx vy

/--
[rayParity_const_of_not_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBridge.lean)
-/
@[path]
private lemma rayParity_const_of_not_vertex_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {vx vy : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hv : ∀ k : Fin n, pos d k ≠ (vx, vy)) :
-- imply
  rayParity d (vx - 1) vy = rayParity d vx vy ∧ rayParity d vx (vy - 1) = rayParity d vx vy ∧ rayParity d (vx - 1) (vy - 1) = rayParity d vx vy := by
-- proof
  apply StatMech.Onsager.WalkCellBridge.rayParity_const_of_not_vertex d hclosed vx vy hv


-- created on 2026-10-23
