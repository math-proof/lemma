import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.LeftCornerE
open StatMech StatMech.Onsager StatMech.Onsager.LeftCornerE


/--
[cornerWeight_leftTurn_E](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/LeftCornerE.lean)
-/
@[path]
private lemma cornerWeight_leftTurn_E_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {i : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hn : 3 ≤ n)
  (hei : d i = 3)
  (he : d (i + 1) = 0) :
-- imply
  cornerWeight (cornerCount (interiorCells d hclosed) (pos d (i + 1))) = if rayParity d (leftCell (d (i + 1)) (pos d (i + 1))).1 (leftCell (d (i + 1)) (pos d (i + 1))).2 = 1 then (1 : ℤ) else -1 := by
-- proof
  apply StatMech.Onsager.LeftCornerE.cornerWeight_leftTurn_E d hclosed hsimple hn i hei he


-- created on 2026-10-23
