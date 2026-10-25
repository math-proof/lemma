import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopGeometricDualWeighted
open Finset StatMech StatMech.Onsager


/--
[kwg_indexedCut_fiber_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopGeometricDualWeighted.lean)
-/
@[path]
private lemma kwg_indexedCut_fiber_card_eq
  {P : PlanarZ2Subgraph}
  {F : Finset (kwg_Edge P)}
-- given
  (hF : kwg_IsEven (kwg_dualEnds P) F) :
-- imply
  ((Finset.univ.filter (fun config : ConfigSpace P.V => kwg_cutSet (kwg_primalEnds P) config = F)).card : Real) = (2 : Real) ^ Nat.card P.G.ConnectedComponent := by
-- proof
  apply StatMech.Onsager.kwg_indexedCut_fiber_card P F hF

/--
[kwg_weightedCutEvenSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopGeometricDualWeighted.lean)
-/
@[path]
private lemma kwg_weightedCutEvenSum_eq
  {P : PlanarZ2Subgraph}
-- given
  (observable : Finset (kwg_Edge P) -> Real) :
-- imply
  (∑ config : ConfigSpace P.V, observable (kwg_cutSet (kwg_primalEnds P) config)) = (2 : Real) ^ Nat.card P.G.ConnectedComponent * ∑ F : Finset (kwg_Edge P), if kwg_IsEven (kwg_dualEnds P) F then observable F else 0 := by
-- proof
  apply StatMech.Onsager.kwg_weightedCutEvenSum P observable


-- created on 2026-10-23
