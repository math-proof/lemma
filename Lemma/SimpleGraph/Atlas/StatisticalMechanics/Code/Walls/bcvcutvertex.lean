import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bcvcutvertex.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bcv_neighbor_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_neighbor_of_walk_eq
  {K : SimpleGraph V}
  {x : V} :
-- imply
  ∀ {a : V}, K.Walk a x → a ≠ x → ∃ w, K.Adj w x ∧ (bkg_deleteVertex K x).Reachable a w := by
-- proof
  apply StatMech.Walls.bcv_neighbor_of_walk

/--
[bcv_deleteVertex_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_deleteVertex_mono_eq
  {T H : SimpleGraph V}
  {x : V}
-- given
  (hTH : T ≤ H) :
-- imply
  bkg_deleteVertex T x ≤ bkg_deleteVertex H x := by
-- proof
  apply StatMech.Walls.bcv_deleteVertex_mono hTH x

/--
[bcv_degree_ge_components](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_degree_ge_components_eq
  [Fintype V]
  {H T : SimpleGraph V}
  [DecidableRel T.Adj]
  {x : V}
  {k : ℕ}
  {a : Fin k → V}
-- given
  (hTH : T ≤ H)
  (hTconn : T.Connected)
  (hne : ∀ i, a i ≠ x)
  (hsep : ∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) :
-- imply
  k ≤ T.degree x := by
-- proof
  apply StatMech.Walls.bcv_degree_ge_components hTH hTconn x a hne hsep

/--
[bcv_spanningTree_degree_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_spanningTree_degree_ge_eq
  [Fintype V]
  {H : SimpleGraph V}
  {x : V}
  {k : ℕ}
  {a : Fin k → V}
-- given
  (hH : H.Connected)
  (hne : ∀ i, a i ≠ x)
  (hsep : ∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) :
-- imply
  ∃ T : SimpleGraph V, T ≤ H ∧ T.IsTree ∧ (∀ (_ : DecidableRel T.Adj), k ≤ T.degree x) := by
-- proof
  apply StatMech.Walls.bcv_spanningTree_degree_ge hH x a hne hsep

/--
[bcv_sep3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_sep3_eq
  {K : SimpleGraph V}
  {b : Fin 3 → V}
-- given
  (h01 : ¬ K.Reachable (b 0) (b 1))
  (h02 : ¬ K.Reachable (b 0) (b 2))
  (h12 : ¬ K.Reachable (b 1) (b 2)) :
-- imply
  ∀ i j, i ≠ j → ¬ K.Reachable (b i) (b j) := by
-- proof
  apply StatMech.Walls.bcv_sep3 h01 h02 h12

/--
[bcv_trif_degree_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_trif_degree_ge_three_eq
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
  apply StatMech.Walls.bcv_trif_degree_ge_three hTH hTconn hne₁ hne₂ hne₃ hsep₁₂ hsep₁₃ hsep₂₃

/--
[bcv_bgnW_test](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_bgnW_test_eq
  {T : SimpleGraph (Fin 8)}
  [DecidableRel T.Adj]
-- given
  (hTH : T ≤ bgn_W)
  (hTconn : T.Connected) :
-- imply
  3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1 := by
-- proof
  apply StatMech.Walls.bcv_bgnW_test hTH hTconn

/--
[bcv_bgnW_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_bgnW_connected_eq :
-- imply
  bgn_W.Connected := by
-- proof
  apply StatMech.Walls.bcv_bgnW_connected

/--
[bcv_bgnW_spanningTree_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_bgnW_spanningTree_deg3_eq :
-- imply
  ∃ T : SimpleGraph (Fin 8), T ≤ bgn_W ∧ T.IsTree ∧ (∀ (_ : DecidableRel T.Adj), 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) := by
-- proof
  apply StatMech.Walls.bcv_bgnW_spanningTree_deg3

/--
[bcv_T0_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_T0_witness_eq :
-- imply
  bcv_T0 ≤ bgn_W ∧ bcv_T0.Connected ∧ bcv_T0.degree 0 = 5 ∧ bcv_T0.degree 1 = 3 ∧ 3 ≤ bcv_T0.degree 0 ∧ 3 ≤ bcv_T0.degree 1 := by
-- proof
  apply StatMech.Walls.bcv_T0_witness

/--
[bcv_globalForest_of_treeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_globalForest_of_treeData_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bcv_ClusterTreeData ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bcv_globalForest_of_treeData ω L R h

/--
[bcv_count_of_treeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_count_of_treeData_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L R : ℕ}
-- given
  (h : bcv_ClusterTreeData ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bcv_count_of_treeData ω L R h

/--
[bcv_bk_of_treeData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_bk_of_treeData_eq
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bcv_bk_of_treeData p hp1 hp0 hdata

/--
[bcv_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean)
-/
@[path]
private lemma bcv_status_eq :
-- imply
  (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj], T ≤ H → T.Connected → ∀ (x : V) {k : ℕ} (a : Fin k → V), (∀ i, a i ≠ x) → (∀ i j, i ≠ j → ¬ (bkg_deleteVertex H x).Reachable (a i) (a j)) → k ≤ T.degree x) ∧ (∀ {V : Type} [Fintype V] {H T : SimpleGraph V} [_i : DecidableRel T.Adj], T ≤ H → T.Connected → ∀ {x a₁ a₂ a₃ : V}, a₁ ≠ x → a₂ ≠ x → a₃ ≠ x → ¬ (bkg_deleteVertex H x).Reachable a₁ a₂ → ¬ (bkg_deleteVertex H x).Reachable a₁ a₃ → ¬ (bkg_deleteVertex H x).Reachable a₂ a₃ → 3 ≤ T.degree x) ∧ (∀ {T : SimpleGraph (Fin 8)} [_i : DecidableRel T.Adj], T ≤ bgn_W → T.Connected → 3 ≤ T.degree 0 ∧ 3 ≤ T.degree 1) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard 2 R) := by
-- proof
  apply StatMech.Walls.bcv_status


-- created on 2026-10-23
