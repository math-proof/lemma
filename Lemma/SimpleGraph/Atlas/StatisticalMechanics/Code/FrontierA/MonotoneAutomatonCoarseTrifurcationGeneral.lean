import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[removeBox_siteForce_eq_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma removeBox_siteForce_eq_general_eq
  {d : ℕ}
  {d n : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  removeSites (bc61_boxAround d n 0) (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) = removeSites (bc61_boxAround d n 0) (siteToBond eta) := by
-- proof
  apply StatMech.FrontierA.removeBox_siteForce_eq_general d n eta

/--
[siteToBond_le_siteForce_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma siteToBond_le_siteForce_general_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  siteToBond eta ≤ siteToBond (forceSitesOccupied (boxFinsetBK d n) eta) := by
-- proof
  apply StatMech.FrontierA.siteToBond_le_siteForce_general n eta

/--
[siteForce_bgfdIndexAllOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma siteForce_bgfdIndexAllOpen_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  BgfdIndexAllOpen (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
-- proof
  apply StatMech.FrontierA.siteForce_bgfdIndexAllOpen n eta

/--
[coarseTrif_siteForce_of_coarse_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma coarseTrif_siteForce_of_coarse_general_eq
  {d : ℕ}
  {n : ℕ}
  {eta : ConfigSpace (Site d)}
-- given
  (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
-- imply
  bc61_IsCoarseTrifurcation (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
-- proof
  apply StatMech.FrontierA.coarseTrif_siteForce_of_coarse_general n eta h

/--
[shell_of_walk_into_box_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma shell_of_walk_into_box_general_eq
  {d : ℕ}
  {L : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {b u x : Site d}
  {w : (openSubgraph d omega).Walk u x} :
-- imply
  Connected d (removeSites (bc61_boxAround d L 0) omega) b u → u ∉ bc61_boxAround d L 0 → x ∈ bc61_boxAround d L 0 → ∃ s t : Site d, (openSubgraph d omega).Adj s t ∧ t ∈ bc61_boxAround d L 0 ∧ Connected d (removeSites (bc61_boxAround d L 0) omega) b s := by
-- proof
  apply StatMech.FrontierA.shell_of_walk_into_box_general w

/--
[attach_of_meetsBox_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma attach_of_meetsBox_general_eq
  {d : ℕ}
  {L : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x x' : Site d}
-- given
  (hinf : (cluster d omega x).Infinite)
  (hx'box : x' ∈ bc61_boxAround d L 0)
  (hxx' : cluster d omega x = cluster d omega x') :
-- imply
  ∃ a : Site d, (∃ bx ∈ bc61_boxAround d L 0, (openSubgraph d omega).Adj bx a) ∧ (cluster d (removeSites (bc61_boxAround d L 0) omega) a).Infinite ∧ cluster d omega x = cluster d omega a := by
-- proof
  apply StatMech.FrontierA.attach_of_meetsBox_general hinf hx'box hxx'

/--
[coarseTrif_of_three_meetBox_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma coarseTrif_of_three_meetBox_general_eq
  {d : ℕ}
  {L : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
-- given
  (hi₁ : (cluster d omega x₁).Infinite)
  (hi₂ : (cluster d omega x₂).Infinite)
  (hi₃ : (cluster d omega x₃).Infinite)
  (hd₁₂ : cluster d omega x₁ ≠ cluster d omega x₂)
  (hd₁₃ : cluster d omega x₁ ≠ cluster d omega x₃)
  (hd₂₃ : cluster d omega x₂ ≠ cluster d omega x₃)
  (hb₁ : x₁ ∈ bc61_boxAround d L 0)
  (hb₂ : x₂ ∈ bc61_boxAround d L 0)
  (hb₃ : x₃ ∈ bc61_boxAround d L 0) :
-- imply
  bc61_IsCoarseTrifurcation omega L 0 := by
-- proof
  apply StatMech.FrontierA.coarseTrif_of_three_meetBox_general hi₁ hi₂ hi₃ hd₁₂ hd₁₃ hd₂₃ hb₁ hb₂ hb₃

/--
[siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ}
-- given
  (h : siteToBond eta ∈ threeMeetBox d n) :
-- imply
  BgfdFaithfulAllOpenTrifAt (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) n 0 := by
-- proof
  apply StatMech.FrontierA.siteForce_bgfdFaithfulAllOpenTrif_of_threeMeetBox eta n h

/--
[measurableSet_siteBgfdFaithfulAllOpenTrifAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma measurableSet_siteBgfdFaithfulAllOpenTrifAt_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  MeasurableSet (SiteBgfdFaithfulAllOpenTrifAt d n) := by
-- proof
  apply StatMech.FrontierA.measurableSet_siteBgfdFaithfulAllOpenTrifAt d n

/--
[exists_siteThreeMeetBox_pos_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma exists_siteThreeMeetBox_pos_general_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (htop : 0 < nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < nu (SiteThreeMeetBoxGeneral d n) := by
-- proof
  apply StatMech.FrontierA.exists_siteThreeMeetBox_pos_general nu htop

/--
[siteBgfdFaithfulAllOpenTrif_pos_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma siteBgfdFaithfulAllOpenTrif_pos_of_top_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (htop : 0 < nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < nu (SiteBgfdFaithfulAllOpenTrifAt d n) := by
-- proof
  apply StatMech.FrontierA.siteBgfdFaithfulAllOpenTrif_pos_of_top nu epsilon hepsilon hinsert htop

/--
[siteBgfdFaithfulAllOpenTrif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma siteBgfdFaithfulAllOpenTrif_prob_eq_zero_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
  {n : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu) :
-- imply
  nu (SiteBgfdFaithfulAllOpenTrifAt d n) = 0 := by
-- proof
  apply StatMech.FrontierA.siteBgfdFaithfulAllOpenTrif_prob_eq_zero nu hd hinv n

/--
[site_cluster_count_top_null_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma site_cluster_count_top_null_general_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} = 0 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_top_null_general nu hd hinv epsilon hepsilon hinsert

/--
[site_cluster_count_ae_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma site_cluster_count_ae_one_general_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hperco : nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1) :
-- imply
  nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_one_general nu hd herg epsilon hepsilon hinsert hperco

/--
[site_cluster_count_ae_zero_or_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma site_cluster_count_ae_zero_or_one_general_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure nu]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu {eta | numInfiniteClusters d (siteToBond eta) = 0} = 1 ∨ nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_zero_or_one_general nu hd herg epsilon hepsilon hinsert

/--
[interpolatedSite_cluster_count_ae_zero_or_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean)
-/
@[path]
private lemma interpolatedSite_cluster_count_ae_zero_or_one_general_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (herg : IsTripleFieldErgodic mu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
-- imply
  (interpolatedSiteLaw T mu) {eta | numInfiniteClusters d (siteToBond eta) = 0} = 1 ∨ (interpolatedSiteLaw T mu) {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_cluster_count_ae_zero_or_one_general T mu hd herg epsilon hepsilon hinsert


-- created on 2026-10-23
