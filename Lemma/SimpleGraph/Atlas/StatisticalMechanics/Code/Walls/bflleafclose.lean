import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bflleafclose
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bfl_tree_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_tree_le_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
-- given
  (hT : T ≤ openSubgraph d ω) :
-- imply
  T ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Walls.bfl_tree_le_lattice hT

/--
[bfl_fineArm_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_fineArm_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w x : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ openSubgraph d ω)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bfl_fineArm_reaches_boundary T hT hR hwx hw hinf

/--
[bfl_treeRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_treeRay_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ openSubgraph d ω)
  (hR : 1 ≤ R)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bfl_treeRay_reaches_boundary T hT hR hw hinf

/--
[bfl_armUnion_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_armUnion_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {Gs : ι → SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hle : ∀ i, Gs i ≤ T) :
-- imply
  (⨆ i, Gs i).IsAcyclic := by
-- proof
  apply StatMech.Walls.bfl_armUnion_acyclic hT Gs hle

/--
[bfl_rayGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_rayGraph_le_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {r : ℕ → V}
  {N : ℕ}
-- given
  (hadj : ∀ k, T.Adj (r k) (r (k + 1))) :
-- imply
  bri_rayGraph r N ≤ T := by
-- proof
  apply StatMech.Walls.bfl_rayGraph_le T r N hadj

/--
[bfl_fineTrif_iff_bc67_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_fineTrif_iff_bc67_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bft_FineTrif ω x ↔ bc67_IsGnTrifurcation ω 0 x := by
-- proof
  apply StatMech.Walls.bfl_fineTrif_iff_bc67_zero ω x

/--
[bfl_fineCount_of_armSubforest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_fineCount_of_armSubforest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {R : ℕ}
-- given
  (h : bau_ArmSubforestData ω 0 R) :
-- imply
  bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bfl_fineCount_of_armSubforest ω R h

/--
[bfl_bk_of_fineArmSubforest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_bk_of_fineArmSubforest_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bfl_bk_of_fineArmSubforest p hp1 hp0 hdata

/--
[bfl_arbitrary_tree_fails_hleaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_arbitrary_tree_fails_hleaf_eq
  {d : ℕ} :
-- imply
  ∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj) (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧ ¬ (∀ v, T.degree v = 1 → v ∈ B) := by
-- proof
  apply StatMech.Walls.bfl_arbitrary_tree_fails_hleaf

/--
[bfl_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bflleafclose.lean)
-/
@[path]
private lemma bfl_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) {T : SimpleGraph (Site 2)}, T ≤ openSubgraph 2 ω → T ≤ hypercubicLattice 2) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ openSubgraph 2 ω → ∀ {w x : Site 2} {R : ℕ}, 1 ≤ R → w ≠ x → w ∈ box 2 R → (ray34_AvoidCluster T {x} w).Infinite → ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧ (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V), (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧ (∃ (G T : SimpleGraph (Fin 4)) (_ : DecidableRel G.Adj) (_ : DecidableRel T.Adj) (B : Finset (Fin 4)), T ≤ G ∧ T.IsTree ∧ (∃ v, G.degree v = 2 ∧ T.degree v = 1 ∧ v ∉ B) ∧ ¬ (∀ v, T.degree v = 1 → v ∈ B)) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (R : ℕ), bau_ArmSubforestData ω 0 R → bc61_coarseTcount ω 0 R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bfl_status


-- created on 2026-10-23
