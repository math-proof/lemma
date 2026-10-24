import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
open StatMech StatMech.FrontierA


/--
[hasRectangularBlockGluing_of_separatelySubadditive_areaBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/RectangularBlockTiling.lean)
-/
@[path]
private lemma hasRectangularBlockGluing_of_separatelySubadditive_areaBound_eq
  {F : Nat -> Nat -> Real}
-- given
  (hF : forall m n, 0 <= F m n)
  (hsub : SeparatelySubadditive F)
  (harea : HasRectangularAreaBound F) :
-- imply
  HasRectangularBlockGluing F := by
-- proof
  apply StatMech.FrontierA.hasRectangularBlockGluing_of_separatelySubadditive_areaBound hF hsub harea


-- created on 2026-10-23
