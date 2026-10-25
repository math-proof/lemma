import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.LeftCornerW
open StatMech StatMech.Onsager StatMech.Onsager.LeftCornerW


/--
[cornerWeight_leftTurn_W](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/LeftCornerW.lean)
-/
@[path]
private lemma cornerWeight_leftTurn_W_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 1)
  (he : d (i + 1) = 2) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = if rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1 (leftCell (d (i + 1)) (pos d (i + 1))).2 = 1 then (1 : ℤ) else -1 := by
-- proof
  apply StatMech.Onsager.LeftCornerW.cornerWeight_leftTurn_W d hclosed hsimple hn i hei he


-- created on 2026-10-23
