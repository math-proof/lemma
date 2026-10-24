import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.ClusterDomination
open Set Filter Topology MeasureTheory StatMech StatMech.BeffaraDC


/--
[geometricTail_of_expDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma geometricTail_of_expDecay_eq
  {d : ℕ}
  {f : ℕ → ℝ}
  {C c : ℝ}
-- given
  (hc : 0 < c)
  (hf : ∀ n, f n ≤ C * Real.exp (-c * n)) :
-- imply
  ∃ r, 0 < r ∧ r < 1 ∧ ∀ n, f n ≤ C * r ^ n := by
-- proof
  apply StatMech.BeffaraDC.geometricTail_of_expDecay hc hf

/--
[crossProb_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma crossProb_geometricTail_eq
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
  ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧ ∀ n, crossProb d p hp n ≤ C * r ^ n := by
-- proof
  apply StatMech.BeffaraDC.crossProb_geometricTail p hp S hoS hphi L hL hSbox

/--
[clusterRadiusDomination_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterRadiusDomination_dist_eq
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
  (clusterRadiusDomination p hp S hoS hphi L hL hSbox).dist = fun n => crossProb d p hp n := by
-- proof
  apply StatMech.BeffaraDC.clusterRadiusDomination_dist p hp S hoS hphi L hL hSbox

/--
[clusterRadiusMoment_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterRadiusMoment_summable_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
  {d' : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  Summable (fun n : ℕ => (n : ℝ) ^ d' * crossProb d p hp n) := by
-- proof
  apply StatMech.BeffaraDC.clusterRadiusMoment_summable p hp S hoS hphi L hL hSbox d'

/--
[clusterRadiusMoment_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterRadiusMoment_lt_top_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
  {d' : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  ∃ C r, 0 ≤ r ∧ r < 1 ∧ clusterMoment (fun n => crossProb d p hp n) d' ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
-- proof
  apply StatMech.BeffaraDC.clusterRadiusMoment_lt_top p hp S hoS hphi L hL hSbox d'

/--
[clusterRadiusMoment_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterRadiusMoment_nonneg_eq
  {d : ℕ}
  {d' : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  0 ≤ clusterMoment (fun n => crossProb d p hp n) d' := by
-- proof
  apply StatMech.BeffaraDC.clusterRadiusMoment_nonneg p hp d'

/--
[crossingEvent_eq_cluster_not_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma crossingEvent_eq_cluster_not_subset_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ∈ crossingEvent d n ↔ ¬ (cluster d ω (origin d) ⊆ box d (n - 1)) := by
-- proof
  apply StatMech.BeffaraDC.crossingEvent_eq_cluster_not_subset n ω

/--
[cluster_finite_card_le_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma cluster_finite_card_le_of_subset_eq
  {d : ℕ}
  {m : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hsub : cluster d ω (origin d) ⊆ box d m) :
-- imply
  ∃ hfin : (cluster d ω (origin d)).Finite, hfin.toFinset.card ≤ (boxFinset d m).card := by
-- proof
  apply StatMech.BeffaraDC.cluster_finite_card_le_of_subset ω hsub

/--
[clusterSize_large_subset_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSize_large_subset_crossing_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hsize : ¬ ∃ hfin : (cluster d ω (origin d)).Finite, hfin.toFinset.card ≤ (boxFinset d (n - 1)).card) :
-- imply
  ω ∈ crossingEvent d n := by
-- proof
  apply StatMech.BeffaraDC.clusterSize_large_subset_crossing n ω hsize

/--
[clusterSize_le_boxCard_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSize_le_boxCard_of_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hfin : (cluster d ω (origin d)).Finite) :
-- imply
  ∃ m, hfin.toFinset.card ≤ (boxFinset d m).card := by
-- proof
  apply StatMech.BeffaraDC.clusterSize_le_boxCard_of_finite ω hfin

/--
[clusterSizeLargeEvent_subset_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSizeLargeEvent_subset_crossing_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  clusterSizeLargeEvent d n ⊆ crossingEvent d n := by
-- proof
  apply StatMech.BeffaraDC.clusterSizeLargeEvent_subset_crossing n

/--
[clusterSizeLargeProb_le_crossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSizeLargeProb_le_crossProb_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterSizeLargeEvent d n) ≤ crossProb d p hp n := by
-- proof
  apply StatMech.BeffaraDC.clusterSizeLargeProb_le_crossProb p hp n

/--
[clusterSizeTail_geometricTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSizeTail_geometricTail_eq
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
  ∃ C, 0 < C ∧ ∃ r, 0 < r ∧ r < 1 ∧ ∀ n, (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterSizeLargeEvent d n) ≤ C * r ^ n := by
-- proof
  apply StatMech.BeffaraDC.clusterSizeTail_geometricTail p hp S hoS hphi L hL hSbox

/--
[clusterSizeMoment_lt_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterDomination.lean)
-/
@[path]
private lemma clusterSizeMoment_lt_top_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {L : ℕ}
  {d' : ℕ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d p hp S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  ∃ C r, 0 ≤ r ∧ r < 1 ∧ clusterMoment (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterSizeLargeEvent d n)) d' ≤ ∑' n : ℕ, (n : ℝ) ^ d' * (C * r ^ n) := by
-- proof
  apply StatMech.BeffaraDC.clusterSizeMoment_lt_top p hp S hoS hphi L hL hSbox d'


-- created on 2026-10-23
