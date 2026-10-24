import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.SurfaceReassembly
open MeasureTheory Set SimpleGraph StatMech StatMech.Percolation


/--
[measurableSet_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma measurableSet_of_dependsOn_eq
  {d : ℕ}
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
-- imply
  MeasurableSet A := by
-- proof
  apply StatMech.Percolation.measurableSet_of_dependsOn hA

/--
[coord_true_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma coord_true_dependsOn_eq
  {d : ℕ}
  {e : E} :
-- imply
  DependsOn (({ω : ConfigSpace E | ω e = true}).indicator (fun _ => (1 : ℝ))) ({e} : Set E) := by
-- proof
  apply StatMech.Percolation.coord_true_dependsOn e

/--
[coord_true_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma coord_true_prob_eq
  {d : ℕ}
  [Countable E]
  [DecidableEq E]
  {e : E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real {ω | ω e = true} = (p : ℝ) := by
-- proof
  apply StatMech.Percolation.coord_true_prob p hp e

/--
[sum_natAbs_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma sum_natAbs_one_eq
  {d : ℕ}
  {n : ℕ}
  {f : Fin n → ℕ}
-- given
  (h : ∑ j, f j = 1) :
-- imply
  ∃ i, f i = 1 ∧ ∀ j, j ≠ i → f j = 0 := by
-- proof
  apply StatMech.Percolation.sum_natAbs_one f h

/--
[adj_coordShift_sr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma adj_coordShift_sr_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  ∃ (i : Fin d) (b : Bool), y = coordShift x i (stepSign b) := by
-- proof
  apply StatMech.Percolation.adj_coordShift_sr x y hadj

/--
[mem_boundaryEdges_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma mem_boundaryEdges_of_adj_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hxS : x ∈ S)
  (hyS : y ∉ S)
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  (x, y) ∈ boundaryEdges d S := by
-- proof
  apply StatMech.Percolation.mem_boundaryEdges_of_adj S hxS hyS hadj

/--
[boundaryEdges_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma boundaryEdges_outer_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {e : Site d × Site d}
-- given
  (he : e ∈ boundaryEdges d S) :
-- imply
  ∃ (i : Fin d) (b : Bool), e.1 ∈ S ∧ e.2 ∉ S ∧ e.2 = coordShift e.1 i (stepSign b) := by
-- proof
  apply StatMech.Percolation.boundaryEdges_outer he

/--
[boundaryEdges_snd_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma boundaryEdges_snd_mem_box_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
  {e : Site d × Site d}
-- given
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1))
  (he : e ∈ boundaryEdges d S) :
-- imply
  e.2 ∈ box d L := by
-- proof
  apply StatMech.Percolation.boundaryEdges_snd_mem_box hL hSbox he

/--
[withinConn_transfer_on_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma withinConn_transfer_on_cluster_eq
  {d : ℕ}
  {S : Set (Site d)}
  {K : Set (Site d)}
  {x : Site d}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hoS : origin d ∈ S)
  (hK : clusterWithin d ω S (origin d) = K)
  (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
  (hconn : ω ∈ withinConnEvent d S (origin d) x) :
-- imply
  ω' ∈ withinConnEvent d S (origin d) x := by
-- proof
  apply StatMech.Percolation.withinConn_transfer_on_cluster hoS hK hagree hconn

/--
[clusterInter_withinConn_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma clusterInter_withinConn_dependsOn_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {K : Finset (Site d)}
  {x : Site d}
-- given
  (hoS : origin d ∈ (S : Set (Site d))) :
-- imply
  DependsOn ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x).indicator (fun _ => (1 : ℝ))) (incidentWithinFinset K S : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.clusterInter_withinConn_dependsOn hoS

/--
[lastExit_summand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma lastExit_summand_factor_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {K : Finset (Site d)}
  {x y : Site d}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hxK : x ∈ K) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω} := by
-- proof
  apply StatMech.Percolation.lastExit_summand_factor p hp S hoS K x y n hxK

/--
[boundaryEdge_disjoint_within](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma boundaryEdge_disjoint_within_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hyS : y ∉ S) :
-- imply
  Disjoint (edgesWithinFinset S) ({s(x, y)} : Finset (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.boundaryEdge_disjoint_within S x y hyS

/--
[withinConn_edge_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma withinConn_edge_indep_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hyS : y ∉ S) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | ω s(x, y) = true}) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) x) * (p : ℝ) := by
-- proof
  apply StatMech.Percolation.withinConn_edge_indep p hp S x y hyS

/--
[crossingEvent_lastExit_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma crossingEvent_lastExit_finset_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {n : ℕ}
-- given
  (hoS : origin d ∈ (S : Set (Site d)))
  (hn : 1 ≤ n)
  (hSbox : (S : Set (Site d)) ⊆ box d (n - 1)) :
-- imply
  crossingEvent d n ⊆ ⋃ K ∈ S.powerset, ⋃ e ∈ boundaryEdges d S, (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) e.1 ∩ {ω | boundaryOpen d (K : Set (Site d)) e.1 e.2 ω} ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) e.2 n ω}) := by
-- proof
  apply StatMech.Percolation.crossingEvent_lastExit_finset S hoS n hn hSbox

/--
[summand_per_K_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma summand_per_K_le_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {K : Finset (Site d)}
  {x y : Site d}
  {L m n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hy : y ∈ box d L)
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) * crossProb d p hp m := by
-- proof
  apply StatMech.Percolation.summand_per_K_le p hp S hoS K x y hy hmLn hm

/--
[sumK_explored_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma sumK_explored_le_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d))) :
-- imply
  ∑ K ∈ S.powerset, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | ω s(x, y) = true}) := by
-- proof
  apply StatMech.Percolation.sumK_explored_le p hp S hoS x y

/--
[sumK_summand_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma sumK_summand_le_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
  {L m n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hyS : y ∉ S)
  (hy : y ∈ box d L)
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  ∑ K ∈ S.powerset, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real ((clusterEvent d (S : Set (Site d)) (origin d) (K : Set (Site d)) ∩ withinConnEvent d (S : Set (Site d)) (origin d) x ∩ {ω | boundaryOpen d (K : Set (Site d)) x y ω}) ∩ {ω | offClusterBoxCrossing d (K : Set (Site d)) y n ω}) ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (withinConnEvent d (S : Set (Site d)) (origin d) x) * (p : ℝ) * crossProb d p hp m := by
-- proof
  apply StatMech.Percolation.sumK_summand_le p hp S hoS x y hyS hy hmLn hm

/--
[subcritical_oneStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma subcritical_oneStep_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
  {k : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1))
  (hk : 1 ≤ k) :
-- imply
  crossProb d p hp ((k + 1) * L) ≤ phi d p hp S * crossProb d p hp (k * L) := by
-- proof
  apply StatMech.Percolation.subcritical_oneStep p hp S hoS L hL hSbox k hk

/--
[geometric_subseq_antitone_decay'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma geometric_subseq_antitone_decay'_eq
  {d : ℕ}
  {f : ℕ → ℝ}
  {r C : ℝ}
  {L : ℕ}
-- given
  (hL : 1 ≤ L)
  (hr0 : 0 < r)
  (hr1 : r < 1)
  (hC : 0 < C)
  (hanti : Antitone f)
  (hsub : ∀ k, f (k * L) ≤ C * r ^ k) :
-- imply
  ∃ c > 0, ∃ C' > 0, ∀ n, f n ≤ C' * Real.exp (-c * n) := by
-- proof
  apply StatMech.Percolation.geometric_subseq_antitone_decay' hL hr0 hr1 hC hanti hsub

/--
[subcritical_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma subcritical_geometric_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, crossProb d p hp (k * L) ≤ r⁻¹ * r ^ k := by
-- proof
  apply StatMech.Percolation.subcritical_geometric p hp S hoS hphi L hL hSbox

/--
[subcritical_decay_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SurfaceReassembly.lean)
-/
@[path]
private lemma subcritical_decay_unconditional_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Percolation.subcritical_decay_unconditional p hp S hoS hphi L hL hSbox


-- created on 2026-10-23
