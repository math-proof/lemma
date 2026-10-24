import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl
open StatMech StatMech.FrontierA


/--
[NewmanRootCumulantRepresentation.newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanRootControl.lean)
-/
@[path]
private lemma newmanFourthCumulantControl_eq
  {cumulants : Nat → Nat → Real}
-- given
  (hroot : NewmanRootCumulantRepresentation cumulants) :
-- imply
  NewmanFourthCumulantControl cumulants := by
-- proof
  apply StatMech.FrontierA.NewmanRootCumulantRepresentation.newmanFourthCumulantControl hroot


-- created on 2026-10-23
