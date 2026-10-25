import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[measurableSet_clusterInfiniteEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma measurableSet_clusterInfiniteEvent_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet (clusterInfiniteEvent d x) := by
-- proof
  apply StatMech.FK.measurableSet_clusterInfiniteEvent x

/--
[two_infinite_clusters_of_not_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma two_infinite_clusters_of_not_connected_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y ⊆ {ω | StatMech.Lattice.Connected d ω x y} ∪ atLeastTwoInfinite d := by
-- proof
  apply StatMech.FK.two_infinite_clusters_of_not_connected x y

/--
[infinite_cluster_inter_le_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma infinite_cluster_inter_le_twoPoint_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ]
  {x y : Site d}
-- given
  (huniq : μ (atLeastTwoInfinite d) = 0) :
-- imply
  μ.real (clusterInfiniteEvent d x ∩ clusterInfiniteEvent d y) ≤ infiniteTwoPointReal μ x y := by
-- proof
  apply StatMech.FK.infinite_cluster_inter_le_twoPoint μ huniq x y

/--
[infiniteTwoPoint_uniform_pos_of_fkg_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma infiniteTwoPoint_uniform_pos_of_fkg_unique_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ]
-- given
  (hPA : ∀ x : Site d, μ.real (clusterInfiniteEvent d (origin d)) * μ.real (clusterInfiniteEvent d x) ≤ μ.real (clusterInfiniteEvent d (origin d) ∩ clusterInfiniteEvent d x))
  (hTI : ∀ x : Site d, μ.real (clusterInfiniteEvent d x) = μ.real (clusterInfiniteEvent d (origin d)))
  (huniq : μ (atLeastTwoInfinite d) = 0)
  (htheta : 0 < μ.real (percolationEvent d)) :
-- imply
  ∃ c : ℝ, 0 < c ∧ ∀ x : Site d, c ≤ infiniteTwoPointReal μ (origin d) x := by
-- proof
  apply StatMech.FK.infiniteTwoPoint_uniform_pos_of_fkg_unique μ hPA hTI huniq htheta

/--
[crossingEvent_real_tendsto_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma crossingEvent_real_tendsto_percolation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ] :
-- imply
  Tendsto (fun n => μ.real (crossingEvent d n)) atTop (nhds (μ.real (percolationEvent d))) := by
-- proof
  apply StatMech.FK.crossingEvent_real_tendsto_percolation μ

/--
[boxBdryConnEvent_real_tendsto_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma boxBdryConnEvent_real_tendsto_percolation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ] :
-- imply
  Tendsto (fun n => μ.real (boxBdryConnEvent d n)) atTop (nhds (μ.real (percolationEvent d))) := by
-- proof
  apply StatMech.FK.boxBdryConnEvent_real_tendsto_percolation μ

/--
[connectionEvent_subset_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma connectionEvent_subset_boxBdryConnEvent_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : x ∉ box d n) :
-- imply
  {ω | StatMech.Lattice.Connected d ω (origin d) x} ⊆ boxBdryConnEvent d n := by
-- proof
  apply StatMech.FK.connectionEvent_subset_boxBdryConnEvent n hn x hx

/--
[infiniteTwoPoint_uniform_decay_of_no_percolation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPositiveFull.lean)
-/
@[path]
private lemma infiniteTwoPoint_uniform_decay_of_no_percolation_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure μ]
-- given
  (htheta : μ.real (percolationEvent d) = 0) :
-- imply
  ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 1 ≤ n ∧ ∀ x : Site d, x ∉ box d n → infiniteTwoPointReal μ (origin d) x < ε := by
-- proof
  apply StatMech.FK.infiniteTwoPoint_uniform_decay_of_no_percolation μ htheta


-- created on 2026-10-23
