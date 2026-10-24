import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bsgspantreegn
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bsg_Gn_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_Gn_le_lattice_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ} :
-- imply
  bgn_Gn ω L ≤ hypercubicLattice d := by
-- proof
  apply StatMech.Walls.bsg_Gn_le_lattice ω L

/--
[bsg_GnTreeRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_GnTreeRay_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ bgn_Gn ω L)
  (hR : 1 ≤ R)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T ∅ w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bsg_GnTreeRay_reaches_boundary ω L T hT hR hw hinf

/--
[bsg_GnBranchRay_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_GnBranchRay_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {T : SimpleGraph (Site d)}
  [LocallyFinite T]
  {w x : Site d}
  {R : ℕ}
-- given
  (hT : T ≤ bgn_Gn ω L)
  (hR : 1 ≤ R)
  (hwx : w ≠ x)
  (hw : w ∈ box d R)
  (hinf : (ray34_AvoidCluster T {x} w).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ≠ x) ∧ (∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bsg_GnBranchRay_reaches_boundary ω L T hT hR hwx hw hinf

/--
[bsg_hub_degree_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_hub_degree_ge_three_eq
  {d : ℕ}
  [Fintype V]
  {H T : SimpleGraph V}
  [DecidableRel T.Adj]
  {x a₁ a₂ a₃ : V}
-- given
  (hTH : T ≤ H)
  (hTconn : T.Connected)
  (hne₁ : a₁ ≠ x)
  (hne₂ : a₂ ≠ x)
  (hne₃ : a₃ ≠ x)
  (hsep₁₂ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₂)
  (hsep₁₃ : ¬ (bkg_deleteVertex H x).Reachable a₁ a₃)
  (hsep₂₃ : ¬ (bkg_deleteVertex H x).Reachable a₂ a₃) :
-- imply
  3 ≤ T.degree x := by
-- proof
  apply StatMech.Walls.bsg_hub_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃

/--
[bsg_bgnW_hubs_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_bgnW_hubs_deg3_eq
  {d : ℕ}
  {T : SimpleGraph (Fin 8)}
  [DecidableRel T.Adj]
-- given
  (hTH : T ≤ bgn_W)
  (hTconn : T.Connected) :
-- imply
  3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1 := by
-- proof
  apply StatMech.Walls.bsg_bgnW_hubs_deg3 hTH hTconn

/--
[bsg_bgnW_spanningTree_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_bgnW_spanningTree_exists_eq
  {d : ℕ} :
-- imply
  ∃ T : SimpleGraph (Fin 8), T ≤ bgn_W ∧ T.IsTree ∧ (∀ (_ : DecidableRel T.Adj), 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) := by
-- proof
  apply StatMech.Walls.bsg_bgnW_spanningTree_exists

/--
[bsg_rayUnion_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_rayUnion_acyclic_eq
  {d : ℕ}
  {T : SimpleGraph V}
  {Gs : ι → SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hGs : ∀ i, Gs i ≤ T) :
-- imply
  (⨆ i, Gs i).IsAcyclic := by
-- proof
  apply StatMech.Walls.bsg_rayUnion_acyclic hT Gs hGs

/--
[bsg_bk_of_treeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_bk_of_treeData_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bsg_bk_of_treeData p hp1 hp0 hdata

/--
[bsg_bk_of_subforestData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_bk_of_subforestData_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bsg_bk_of_subforestData p hp1 hp0 hdata

/--
[bsg_datum_implies_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_datum_implies_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bau_ArmSubforestData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bsg_datum_implies_count ω L R h

/--
[bsg_twoHub_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_twoHub_witness_eq
  {d : ℕ} :
-- imply
  bri_twoHub.IsTree ∧ bri_twoHub.degree 0 = 3 ∧ bri_twoHub.degree 1 = 3 ∧ bri_twoHub.degree 4 = 2 ∧ (∀ v : Fin 7, v ∉ ({2, 3, 5, 6} : Finset (Fin 7)) → 2 ≤ bri_twoHub.degree v) := by
-- proof
  apply StatMech.Walls.bsg_twoHub_witness

/--
[bsg_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bsgspantreegn.lean)
-/
@[path]
private lemma bsg_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bgn_Gn ω L ≤ hypercubicLattice 2) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (T : SimpleGraph (Site 2)) [LocallyFinite T], T ≤ bgn_Gn ω L → ∀ {w : Site 2} {R : ℕ}, 1 ≤ R → w ∈ box 2 R → (ray34_AvoidCluster T ∅ w).Infinite → ∃ r : ℕ → Site 2, r 0 = w ∧ Function.Injective r ∧ (∀ k, T.Adj (r k) (r (k + 1))) ∧ (∃ k, r k ∈ vertexBoundary 2 R)) ∧ (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected → 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧ (∀ {V : Type} {T : SimpleGraph V}, T.IsTree → ∀ {ι : Type} (Gs : ι → SimpleGraph V), (∀ i, Gs i ≤ T) → (⨆ i, Gs i).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bau_ArmSubforestData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bsg_status


-- created on 2026-10-23
