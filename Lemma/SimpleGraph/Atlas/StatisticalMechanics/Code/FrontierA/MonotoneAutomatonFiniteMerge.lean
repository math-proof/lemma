import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[mem_boxFinsetBK_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma mem_boxFinsetBK_iff_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d} :
-- imply
  x ∈ boxFinsetBK d n ↔ x ∈ box d n := by
-- proof
  apply StatMech.FrontierA.mem_boxFinsetBK_iff

/--
[box_subset_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma box_subset_box_succ_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  box d n ⊆ box d (n + 1) := by
-- proof
  apply StatMech.FrontierA.box_subset_box_succ n

/--
[mem_box_of_forceSitesOccupied_true_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma mem_box_of_forceSitesOccupied_true_of_false_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
  {x : Site d}
-- given
  (hforced : forceSitesOccupied (boxFinsetBK d n) eta x = true)
  (hclosed : eta x = false) :
-- imply
  x ∈ box d n := by
-- proof
  apply StatMech.FrontierA.mem_box_of_forceSitesOccupied_true_of_false n eta x hforced hclosed

/--
[openSubgraph_siteForce_eq_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma openSubgraph_siteForce_eq_forceOpen_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  openSubgraph d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) = openSubgraph d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) := by
-- proof
  apply StatMech.FrontierA.openSubgraph_siteForce_eq_forceOpen n eta

/--
[connected_siteForce_iff_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma connected_siteForce_iff_forceOpen_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y ↔ Connected d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x y := by
-- proof
  apply StatMech.FrontierA.connected_siteForce_iff_forceOpen n eta x y

/--
[cluster_siteForce_eq_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma cluster_siteForce_eq_forceOpen_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  cluster d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x = cluster d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) x := by
-- proof
  apply StatMech.FrontierA.cluster_siteForce_eq_forceOpen n eta x

/--
[numInfiniteClusters_siteForce_eq_forceOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_siteForce_eq_forceOpen_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  numInfiniteClusters d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) = numInfiniteClusters d (forceOpenFinset (siteForceEdges n eta) (siteToBond eta)) := by
-- proof
  apply StatMech.FrontierA.numInfiniteClusters_siteForce_eq_forceOpen n eta

/--
[siteForce_box_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma siteForce_box_connected_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  Connected d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) x y := by
-- proof
  apply StatMech.FrontierA.siteForce_box_connected n eta hx hy

/--
[numInfiniteClusters_siteForce_lt_of_twoMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_siteForce_lt_of_twoMeetBox_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d}
-- given
  (hfin : numInfiniteClusters d (siteToBond eta) ≠ ⊤)
  (hxbox : x ∈ box d n)
  (hybox : y ∈ box d n)
  (hx : (cluster d (siteToBond eta) x).Infinite)
  (hy : (cluster d (siteToBond eta) y).Infinite)
  (hne : cluster d (siteToBond eta) x ≠ cluster d (siteToBond eta) y) :
-- imply
  numInfiniteClusters d (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) < numInfiniteClusters d (siteToBond eta) := by
-- proof
  apply StatMech.FrontierA.numInfiniteClusters_siteForce_lt_of_twoMeetBox n eta hfin hxbox hybox hx hy hne

/--
[exists_siteTwoMeetBox_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma exists_siteTwoMeetBox_pos_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
  {k : ℕ∞}
-- given
  (hk2 : 2 ≤ k)
  (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) :
-- imply
  ∃ n : ℕ, 0 < nu (SiteTwoMeetBox (d := d) n k) := by
-- proof
  apply StatMech.FrontierA.exists_siteTwoMeetBox_pos nu hk2 hk

/--
[finite_constant_cluster_count_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma finite_constant_cluster_count_impossible_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
  {k : ℕ∞}
-- given
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hk2 : 2 ≤ k)
  (hktop : k ≠ ⊤)
  (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) :
-- imply
  False := by
-- proof
  apply StatMech.FrontierA.finite_constant_cluster_count_impossible nu epsilon hepsilon hinsert hk2 hktop hk

/--
[site_cluster_count_ae_lt_two_or_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma site_cluster_count_ae_lt_two_or_infinite_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  ∃ k : ℕ∞, nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1 ∧ (¬ 2 ≤ k ∨ k = ⊤) := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_lt_two_or_infinite nu herg epsilon hepsilon hinsert

/--
[site_cluster_count_ae_one_or_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean)
-/
@[path]
private lemma site_cluster_count_ae_one_or_infinite_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hperco : nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1) :
-- imply
  nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 ∨ nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} = 1 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_one_or_infinite nu herg epsilon hepsilon hinsert hperco


-- created on 2026-10-23
