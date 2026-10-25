import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryWindingPersistence
open Equiv SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectNonzeroBlackBoundaryWinding_persists_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryWindingPersistence.lean)
-/
@[path]
private lemma fkRectNonzeroBlackBoundaryWinding_persists_insert_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (heF : e ∉ F)
  (hnewNoNet : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R (insert e F)))
  (hdne : fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F)) d ≠ 0) :
-- imply
  ∃ d' : FKMedialBlackDart R.medialTorus, fkRectBlackBoundaryCycleClassWinding R (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) d' ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectNonzeroBlackBoundaryWinding_persists_insert R F e heF hnewNoNet d hdne


-- created on 2026-10-23
