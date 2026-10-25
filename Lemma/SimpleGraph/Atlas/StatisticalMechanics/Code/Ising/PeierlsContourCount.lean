import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
open MeasureTheory Filter Topology Finset SimpleGraph StatMech StatMech.Ising


/--
[pcc_crossEdges_subset_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_crossEdges_subset_biUnion_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {n : ℕ} :
-- imply
  crossEdges (↑K) (bondFinsetTouch d n) ⊆ K.biUnion (fun v => (hypercubicLattice d).incidenceFinset v) := by
-- proof
  apply StatMech.Ising.pcc_crossEdges_subset_biUnion K n

/--
[pcc_contourLen_le_card_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_contourLen_le_card_mul_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {n : ℕ} :
-- imply
  contourLen (↑K) (bondFinsetTouch d n) ≤ 2 * d * K.card := by
-- proof
  apply StatMech.Ising.pcc_contourLen_le_card_mul K n

/--
[pcc_pairCluster_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_pairCluster_card_le_eq
  {d : ℕ}
  {p : Site d} :
-- imply
  (pcc_pairCluster p).card ≤ 2 := by
-- proof
  apply StatMech.Ising.pcc_pairCluster_card_le p

/--
[pcc_pairCluster_contourLen_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_pairCluster_contourLen_le_eq
  {d : ℕ}
  {p : Site d}
  {n : ℕ} :
-- imply
  contourLen (↑(pcc_pairCluster p)) (bondFinsetTouch d n) ≤ 2 * d * 2 := by
-- proof
  apply StatMech.Ising.pcc_pairCluster_contourLen_le p n

/--
[pcc_pairCluster_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_pairCluster_injOn_eq
  {d : ℕ} :
-- imply
  Set.InjOn (pcc_pairCluster (d := d)) {p | p ≠ origin d} := by
-- proof
  apply StatMech.Ising.pcc_pairCluster_injOn

/--
[pcc_pairCluster_mem_originFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_pairCluster_mem_originFamily_eq
  {d : ℕ}
  {n : ℕ}
  {p : Site d}
-- given
  (hp : p ∈ boxFinset d n) :
-- imply
  pcc_pairCluster p ∈ originClusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.pcc_pairCluster_mem_originFamily hp

/--
[pcc_originSum_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_originSum_ge_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  (((boxFinset d n).erase (origin d)).card : ℝ) * Real.exp (-(2 * β) * (2 * d * 2 : ℕ)) ≤ ∑ K ∈ originClusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.pcc_originSum_ge n β hβ

/--
[pcc_rayS_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_rayS_coord_eq
  {d : ℕ}
  {c : Fin d}
  {j : ℕ} :
-- imply
  (pcc_rayS c j) c = (j : ℤ) := by
-- proof
  apply StatMech.Ising.pcc_rayS_coord c j

/--
[pcc_rayS_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_rayS_ne_origin_eq
  {d : ℕ}
  {c : Fin d}
  {j : ℕ}
-- given
  (hj : 0 < j) :
-- imply
  pcc_rayS c j ≠ origin d := by
-- proof
  apply StatMech.Ising.pcc_rayS_ne_origin c hj

/--
[pcc_n_le_erase_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_n_le_erase_card_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  n ≤ ((boxFinset d n).erase (origin d)).card := by
-- proof
  apply StatMech.Ising.pcc_n_le_erase_card hd n

/--
[pcc_originSum_unbounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_originSum_unbounded_eq
  {d : ℕ}
  {β : ℝ}
  {M : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β) :
-- imply
  ∃ n : ℕ, M < ∑ K ∈ originClusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.pcc_originSum_unbounded hd β hβ M

/--
[pcc_not_originContourCountBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_not_originContourCountBound_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β) :
-- imply
  ∃ n : ℕ, ¬ OriginContourCountBound d n β := by
-- proof
  apply StatMech.Ising.pcc_not_originContourCountBound hd β hβ

/--
[pcc_originContourCount_hypothesis_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_originContourCount_hypothesis_false_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ¬ ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → OriginContourCountBound d n β := by
-- proof
  apply StatMech.Ising.pcc_originContourCount_hypothesis_false hd

/--
[pcc_mem_connClusterFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_mem_connClusterFamily_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)} :
-- imply
  K ∈ connClusterFamily (d := d) n ↔ K ∈ clusterFamily (d := d) n ∧ IsConnectedCluster K := by
-- proof
  apply StatMech.Ising.pcc_mem_connClusterFamily

/--
[pcc_connFamily_subset_originFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_connFamily_subset_originFamily_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  connClusterFamily (d := d) n ⊆ originClusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.pcc_connFamily_subset_originFamily n

/--
[pcc_walk_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_walk_transfer_eq
  {d : ℕ}
  {σ : ConfigSpace (Site d)}
  {o : Site d} :
-- imply
  ∀ {a x : Site d}, (minusGraph σ).Walk a x → a ∈ minusCluster σ o → (latticeOn (minusCluster σ o)).Reachable a x := by
-- proof
  apply StatMech.Ising.pcc_walk_transfer

/--
[pcc_minusClusterFinset_isConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_minusClusterFinset_isConnected_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  IsConnectedCluster (minusClusterFinset τ ho) := by
-- proof
  apply StatMech.Ising.pcc_minusClusterFinset_isConnected τ ho

/--
[pcc_minusClusterFinset_mem_connFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_minusClusterFinset_mem_connFamily_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (ho : glue (plusField d) τ (origin d) = false) :
-- imply
  minusClusterFinset τ ho ∈ connClusterFamily (d := d) n := by
-- proof
  apply StatMech.Ising.pcc_minusClusterFinset_mem_connFamily τ ho

/--
[pcc_probOriginMinus_le_sum_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_probOriginMinus_le_sum_conn_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ connClusterFamily (d := d) n, probContour (↑K) (plusField d) n (bondFinsetTouch d n) β := by
-- proof
  apply StatMech.Ising.pcc_probOriginMinus_le_sum_conn n β

/--
[pcc_probOriginMinus_le_sum_exp_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_probOriginMinus_le_sum_exp_conn_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ} :
-- imply
  probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 ≤ ∑ K ∈ connClusterFamily (d := d) n, Real.exp (-(2 * β) * (contourLen (↑K) (bondFinsetTouch d n) : ℝ)) := by
-- proof
  apply StatMech.Ising.pcc_probOriginMinus_le_sum_exp_conn n β

/--
[pcc_peierlsContourBound_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_peierlsContourBound_of_connected_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
-- given
  (hCount : ConnectedContourCountBound d n β) :
-- imply
  PeierlsContourBound d n β := by
-- proof
  apply StatMech.Ising.pcc_peierlsContourBound_of_connected n β hCount

/--
[pcc_peierls_long_range_order_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean)
-/
@[path]
private lemma pcc_peierls_long_range_order_of_connected_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → ConnectedContourCountBound d n β) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
-- proof
  apply StatMech.Ising.pcc_peierls_long_range_order_of_connected hd hCount


-- created on 2026-10-23
