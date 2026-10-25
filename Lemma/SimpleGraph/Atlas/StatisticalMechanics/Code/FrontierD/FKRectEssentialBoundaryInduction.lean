import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEssentialBoundaryInduction
open SimpleGraph StatMech StatMech.FrontierD


/--
[exists_nonzero_blackBoundaryWinding_of_closedWalk_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEssentialBoundaryInduction.lean)
-/
@[path]
private lemma exists_nonzero_blackBoundaryWinding_of_closedWalk_of_not_hasNet_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x : R.Vertex}
  {q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x x}
-- given
  (hnoNet : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hqne : fkRectWalkWinding R q ≠ (0, 0)) :
-- imply
  ∃ d : FKMedialBlackDart R.medialTorus, fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) d ≠ 0 := by
-- proof
  apply StatMech.FrontierD.exists_nonzero_blackBoundaryWinding_of_closedWalk_of_not_hasNet R F x q hnoNet hqne


-- created on 2026-10-23
