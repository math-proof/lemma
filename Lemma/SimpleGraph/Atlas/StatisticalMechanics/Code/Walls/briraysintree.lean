import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.briraysintree.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bri_treeRay_of_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_treeRay_of_infiniteComponent_eq
  {d : ℕ}
  [DecidableEq V]
  {T : SimpleGraph V}
  [LocallyFinite T]
  {w : V}
-- given
  (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
-- imply
  ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) := by
-- proof
  apply StatMech.Walls.bri_treeRay_of_infiniteComponent T hinf

/--
[bri_branchRay_avoiding_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_branchRay_avoiding_vertex_eq
  {d : ℕ}
  [DecidableEq V]
  {T : SimpleGraph V}
  [LocallyFinite T]
  {w x : V}
-- given
  (hwx : w ≠ x)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → V, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) := by
-- proof
  apply StatMech.Walls.bri_branchRay_avoiding_vertex T hwx hinf

/--
[bri_treeRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_treeRay_reaches_boundary_eq
  {d : ℕ}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w : Site d}
  {R : ℕ}
-- given
  (hle : T ≤ hypercubicLattice d)
  (hR : 1 ≤ R)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bri_treeRay_reaches_boundary T hle hR hw hinf

/--
[bri_branchRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_branchRay_reaches_boundary_eq
  {d : ℕ}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w x : Site d}
  {R : ℕ}
-- given
  (hle : T ≤ hypercubicLattice d)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bri_branchRay_reaches_boundary T hle hR hwx hw hinf

/--
[bri_rayGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_rayGraph_le_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {r : ℕ → V}
  {N : ℕ}
-- given
  (hadj : ∀ k, T.Adj (r k) (r (k + 1))) :
-- imply
  bri_rayGraph r N ≤ T := by
-- proof
  apply StatMech.Walls.bri_rayGraph_le T r N hadj

/--
[bri_rayGraph_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_rayGraph_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {r : ℕ → V}
  {N : ℕ}
-- given
  (hT : T.IsTree)
  (hadj : ∀ k, T.Adj (r k) (r (k + 1))) :
-- imply
  (bri_rayGraph r N).IsAcyclic := by
-- proof
  apply StatMech.Walls.bri_rayGraph_acyclic hT r N hadj

/--
[bri_union_le_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_union_le_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {Gs : ι → SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hGs : ∀ i, Gs i ≤ T) :
-- imply
  (⨆ i, Gs i).IsAcyclic := by
-- proof
  apply StatMech.Walls.bri_union_le_acyclic hT Gs hGs

/--
[bri_two_rays_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_two_rays_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {r s : ℕ → V}
  {N M : ℕ}
-- given
  (hT : T.IsTree)
  (hr : ∀ k, T.Adj (r k) (r (k + 1)))
  (hs : ∀ k, T.Adj (s k) (s (k + 1))) :
-- imply
  (bri_rayGraph r N ⊔ bri_rayGraph s M).IsAcyclic := by
-- proof
  apply StatMech.Walls.bri_two_rays_acyclic hT r s N M hr hs

/--
[bri_twoHub_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_twoHub_witness_eq
  {d : ℕ} :
-- imply
  bri_twoHub.IsTree ∧ bri_twoHub.IsAcyclic ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧ bri_twoHub.degree 4 = 2 ∧ bri_twoHub.degree 2 = 1 ∧ bri_twoHub.degree 3 = 1 ∧ bri_twoHub.degree 5 = 1 ∧ bri_twoHub.degree 6 = 1 ∧ (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) := by
-- proof
  apply StatMech.Walls.bri_twoHub_witness

/--
[bri_twoHub_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_twoHub_count_eq
  {d : ℕ} :
-- imply
  ({0, 1} : Finset (Fin 7)).card ≤ ({2, 3, 5, 6} : Finset (Fin 7)).card := by
-- proof
  apply StatMech.Walls.bri_twoHub_count

/--
[bri_bk_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_bk_of_subforestData_eq
  {d : ℕ}
-- given
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bri_bk_of_subforestData p hp1 hp0 hdata

/--
[bri_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_datum_implies_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bri_datum_implies_count ω L R h

/--
[bri_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/briraysintree.lean)
-/
@[path]
private lemma bri_status_eq
  {d : ℕ} :
-- imply
  (∀ (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ hypercubicLattice 2 → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R → (ray34_AvoidCluster T {x} w).Infinite → ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧ (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V), (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧ (bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧ bri_twoHub.degree 4 = 2 ∧ (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (p : NNReal) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bri_status


-- created on 2026-10-23
