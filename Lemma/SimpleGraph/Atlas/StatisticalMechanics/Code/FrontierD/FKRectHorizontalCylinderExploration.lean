import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinder_bottomRoot_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_bottomRoot_mem_eq
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {x : Fin R.width}
-- given
  (hx : x ∈ S) :
-- imply
  (x, fkRectBottomRow R) ∈ fkRectHorizontalCylinderBottomRoots R S := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_bottomRoot_mem R S hx

/--
[fkRectHorizontalCylinderExploredVertex_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderExploredVertex_iff_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {v : R.Vertex} :
-- imply
  FKRectHorizontalCylinderExploredVertex R rho S v ↔ ∃ x ∈ S, (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable (x, fkRectBottomRow R) v := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderExploredVertex_iff R rho S v

/--
[not_horizontalCylinderExplored_of_fresh_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma not_horizontalCylinderExplored_of_fresh_reachable_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {T S : Finset (Fin R.width)}
  {x : Fin R.width}
  {v : R.Vertex}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
  (hST : S ⊆ T)
  (hxT : x ∈ T)
  (hxS : x ∉ S)
  (hxv : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable (x, fkRectBottomRow R) v) :
-- imply
  ¬ FKRectHorizontalCylinderExploredVertex R rho S v := by
-- proof
  apply StatMech.FrontierD.not_horizontalCylinderExplored_of_fresh_reachable R rho pair T S hW hST hxT hxS hxv

/--
[not_horizontalCylinderExplored_fresh_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma not_horizontalCylinderExplored_fresh_source_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {T S : Finset (Fin R.width)}
  {x : Fin R.width}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
  (hST : S ⊆ T)
  (hxT : x ∈ T)
  (hxS : x ∉ S) :
-- imply
  ¬ FKRectHorizontalCylinderExploredVertex R rho S (x, fkRectBottomRow R) := by
-- proof
  apply StatMech.FrontierD.not_horizontalCylinderExplored_fresh_source R rho pair T S hW hST hxT hxS

/--
[horizontalCylinderUnexplored_openAdj_of_fresh_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma horizontalCylinderUnexplored_openAdj_of_fresh_reachable_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {T S : Finset (Fin R.width)}
  {x : Fin R.width}
  {u v : R.Vertex}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
  (hST : S ⊆ T)
  (hxT : x ∈ T)
  (hxS : x ∉ S)
  (hxu : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Reachable (x, fkRectBottomRow R) u)
  (huv : (FK.openSub (fkRectHorizontalCylinderGraph R) rho).Adj u v) :
-- imply
  (FK.openSub (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) (FK.ocd_innerRestrict (Subtype.val : FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex) rho)).Adj (⟨u, not_horizontalCylinderExplored_of_fresh_reachable R rho pair T S hW hST hxT hxS hxu⟩) (⟨v, not_horizontalCylinderExplored_of_fresh_reachable R rho pair T S hW hST hxT hxS (hxu.trans huv.reachable)⟩) := by
-- proof
  apply StatMech.FrontierD.horizontalCylinderUnexplored_openAdj_of_fresh_reachable R rho pair T S hW hST hxT hxS hxu huv

/--
[horizontalCylinderUnexplored_reachable_of_fresh_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma horizontalCylinderUnexplored_reachable_of_fresh_pair_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {T S : Finset (Fin R.width)}
  {x : Fin R.width}
-- given
  (pair : Fin R.width -> Fin R.width)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair T rho)
  (hST : S ⊆ T)
  (hxT : x ∈ T)
  (hxS : x ∉ S) :
-- imply
  ∃ source target : FKRectHorizontalCylinderUnexploredVertex R rho S, source.1 = (x, fkRectBottomRow R) ∧ target.1 = (pair x, fkRectTopRow R) ∧ (FK.openSub (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) (FK.ocd_innerRestrict (Subtype.val : FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex) rho)).Reachable source target := by
-- proof
  apply StatMech.FrontierD.horizontalCylinderUnexplored_reachable_of_fresh_pair R rho pair T S hW hST hxT hxS

/--
[fkRectHorizontalCylinder_condBcProb_eq_freeUnexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_condBcProb_eq_freeUnexplored_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {p q : Real}
  {omega : ConfigSpace (Sym2 (FKRectHorizontalCylinderUnexploredVertex R rho S))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  FK.condBcProb (fkRectHorizontalCylinderGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (FK.clusterUnexploredPairEdges (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) rho (@FK.ocd_psiExt (FKRectHorizontalCylinderUnexploredVertex R rho S) R.Vertex (FK.instFintypeClusterUnexploredVertex (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) (by infer_instance) (Subtype.val : FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex) rho omega) = FK.fkProb (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) p q omega := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_condBcProb_eq_freeUnexplored R rho S hp hp1 hq omega

/--
[fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderExploration.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (FKRectHorizontalCylinderUnexploredVertex R rho S)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (∑ sigma : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectHorizontalCylinderUnexploredVertex R rho S -> R.Vertex) ⁻¹' A).indicator (fun _ => (1 : Real)) sigma * FK.condBcProb (fkRectHorizontalCylinderGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (FK.clusterUnexploredPairEdges (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) rho sigma) = ∑ omega, A.indicator (fun _ => (1 : Real)) omega * FK.fkProb (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) p q omega := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored R rho S hp hp1 hq A


-- created on 2026-10-23
