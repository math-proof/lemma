import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcation
open MeasureTheory Set StatMech StatMech.FrontierA


/--
[removeBox_siteForce_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma removeBox_siteForce_eq_eq
  {n : ℕ}
  {eta : ConfigSpace (Site 2)} :
-- imply
  removeSites (bc61_boxAround 2 n 0) (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) = removeSites (bc61_boxAround 2 n 0) (siteToBond eta) := by
-- proof
  apply StatMech.FrontierA.removeBox_siteForce_eq n eta

/--
[siteToBond_le_siteForce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma siteToBond_le_siteForce_eq
  {n : ℕ}
  {eta : ConfigSpace (Site 2)} :
-- imply
  siteToBond eta ≤ siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta) := by
-- proof
  apply StatMech.FrontierA.siteToBond_le_siteForce n eta

/--
[siteForce_box_allOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma siteForce_box_allOpen_eq
  {n : ℕ}
  {eta : ConfigSpace (Site 2)} :
-- imply
  bff_BoxAllOpen (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n := by
-- proof
  apply StatMech.FrontierA.siteForce_box_allOpen n eta

/--
[coarseTrif_siteForce_of_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma coarseTrif_siteForce_of_coarse_eq
  {n : ℕ}
  {eta : ConfigSpace (Site 2)}
-- given
  (h : bc61_IsCoarseTrifurcation (siteToBond eta) n 0) :
-- imply
  bc61_IsCoarseTrifurcation (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
-- proof
  apply StatMech.FrontierA.coarseTrif_siteForce_of_coarse n eta h

/--
[siteForce_faithfulAllOpenTrif_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma siteForce_faithfulAllOpenTrif_of_threeMeetBox_eq
  {eta : ConfigSpace (Site 2)}
  {n : ℕ}
-- given
  (h : siteToBond eta ∈ threeMeetBox 2 n) :
-- imply
  FaithfulAllOpenTrifAt (siteToBond (forceSitesOccupied (boxFinsetBK 2 n) eta)) n 0 := by
-- proof
  apply StatMech.FrontierA.siteForce_faithfulAllOpenTrif_of_threeMeetBox eta n h

/--
[measurableSet_siteFaithfulAllOpenTrifAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma measurableSet_siteFaithfulAllOpenTrifAt_eq
  {n : ℕ} :
-- imply
  MeasurableSet (SiteFaithfulAllOpenTrifAt n) := by
-- proof
  apply StatMech.FrontierA.measurableSet_siteFaithfulAllOpenTrifAt n

/--
[exists_siteThreeMeetBox_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma exists_siteThreeMeetBox_pos_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
-- given
  (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < nu (SiteThreeMeetBox n) := by
-- proof
  apply StatMech.FrontierA.exists_siteThreeMeetBox_pos nu htop

/--
[siteFaithfulAllOpenTrif_pos_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma siteFaithfulAllOpenTrif_pos_of_top_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
-- given
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
-- imply
  ∃ n : ℕ, 0 < nu (SiteFaithfulAllOpenTrifAt n) := by
-- proof
  apply StatMech.FrontierA.siteFaithfulAllOpenTrif_pos_of_top nu epsilon hepsilon hinsert htop

/--
[siteFaithfulAllOpenTrif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma siteFaithfulAllOpenTrif_prob_eq_zero_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu) :
-- imply
  nu (SiteFaithfulAllOpenTrifAt n) = 0 := by
-- proof
  apply StatMech.FrontierA.siteFaithfulAllOpenTrif_prob_eq_zero nu hinv n

/--
[site_cluster_count_top_null_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma site_cluster_count_top_null_two_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤} = 0 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_top_null_two nu hinv epsilon hepsilon hinsert

/--
[site_cluster_count_ae_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma site_cluster_count_ae_one_two_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
-- given
  (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hperco : nu {eta | 1 ≤ numInfiniteClusters 2 (siteToBond eta)} = 1) :
-- imply
  nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_one_two nu herg epsilon hepsilon hinsert hperco

/--
[site_cluster_count_ae_zero_or_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma site_cluster_count_ae_zero_or_one_two_eq
  {nu : Measure (ConfigSpace (Site 2))}
  [IsProbabilityMeasure nu]
-- given
  (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨ nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.site_cluster_count_ae_zero_or_one_two nu herg epsilon hepsilon hinsert

/--
[interpolatedSite_cluster_count_ae_zero_or_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean)
-/
@[path]
private lemma interpolatedSite_cluster_count_ae_zero_or_one_two_eq
  {T : MonotoneAutomaton 2}
  {mu : Measure (FieldTriple 2)}
  [IsProbabilityMeasure mu]
-- given
  (herg : IsTripleFieldErgodic mu)
  (epsilon : ℝ≥0∞)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
-- imply
  (interpolatedSiteLaw T mu) {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨ (interpolatedSiteLaw T mu) {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_cluster_count_ae_zero_or_one_two T mu herg epsilon hepsilon hinsert


-- created on 2026-10-23
