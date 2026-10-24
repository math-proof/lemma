import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderAdaptiveProjection
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderAdaptiveProjection_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderAdaptiveProjection_idem_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectHorizontalCylinderAdaptiveProjection R S (fkRectHorizontalCylinderAdaptiveProjection R S rho) = fkRectHorizontalCylinderAdaptiveProjection R S rho := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderAdaptiveProjection_idem R S rho

/--
[fkRectHorizontalCylinderAdaptiveInsideEdges_eq_clusterPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderAdaptiveInsideEdges_eq_clusterPairs_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  fkRectHorizontalCylinderAdaptiveInsideEdges R S rho = FK.clusterUnexploredPairEdges (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderAdaptiveInsideEdges_eq_clusterPairs R S rho

/--
[fkRectHorizontalCylinderExploredVertex_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderExploredVertex_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {v : R.Vertex} :
-- imply
  FKRectHorizontalCylinderExploredVertex R (fkRectHorizontalCylinderAdaptiveProjection R S rho) S v ↔ FKRectHorizontalCylinderExploredVertex R rho S v := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderExploredVertex_projection_iff R S rho v

/--
[fkRectHorizontalCylinderSourceReachable_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderSourceReachable_projection_iff_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {x : Fin R.width}
  {v : R.Vertex}
-- given
  (hx : x ∈ S) :
-- imply
  (FK.openSub (fkRectHorizontalCylinderGraph R) (fkRectHorizontalCylinderAdaptiveProjection R S rho)).Reachable (x, fkRectBottomRow R) v ↔ (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable (x, fkRectBottomRow R) v := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderSourceReachable_projection_iff R S rho hx v

/--
[fkRectHorizontalCylinderDistinctPairedWitness_projection_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_projection_iff_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
  {rho : ConfigSpace (Sym2 R.Vertex)} :
-- imply
  FKRectHorizontalCylinderDistinctPairedWitness R pair S (fkRectHorizontalCylinderAdaptiveProjection R S rho) ↔ FKRectHorizontalCylinderDistinctPairedWitness R pair S rho := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_projection_iff R pair S rho

/--
[fkRectHorizontalCylinderDistinctPairedWitness_fibre_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_fibre_iff_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hproj : fkRectHorizontalCylinderAdaptiveProjection R S rho = fkRectHorizontalCylinderAdaptiveProjection R S sigma) :
-- imply
  FKRectHorizontalCylinderDistinctPairedWitness R pair S rho ↔ FKRectHorizontalCylinderDistinctPairedWitness R pair S sigma := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_fibre_iff R pair S hproj

/--
[fkRectHorizontalCylinderAdaptiveProjection_filter_eq_condFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderAdaptiveProjection_filter_eq_condFibre_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {psi : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hpsi : fkRectHorizontalCylinderAdaptiveProjection R S psi = psi) :
-- imply
  Finset.univ.filter (fun rho => fkRectHorizontalCylinderAdaptiveProjection R S rho = psi) = FK.condFibre (fkRectHorizontalCylinderAdaptiveInsideEdges R S psi) psi := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderAdaptiveProjection_filter_eq_condFibre R S psi hpsi

/--
[fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveProjection.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_base_eq
  {R : FKRectTorus}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
  {x : Fin R.width}
  {rho : ConfigSpace (Sym2 R.Vertex)}
-- given
  (h : FKRectHorizontalCylinderDistinctPairedWitness R pair (insert x S) rho) :
-- imply
  FKRectHorizontalCylinderDistinctPairedWitness R pair S rho := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_insert_imp_base R pair S x rho h


-- created on 2026-10-23
