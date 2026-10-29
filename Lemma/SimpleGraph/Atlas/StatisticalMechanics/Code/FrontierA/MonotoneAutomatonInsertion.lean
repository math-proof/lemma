import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
open MeasureTheory StatMech StatMech.FrontierA


/--
[tripleEventIgnoresMiddleAt_preimage_interpolatedSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma tripleEventIgnoresMiddleAt_preimage_interpolatedSite_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {x : Site d}
  {B : Set (ConfigSpace (Site d))}
-- given
  (hB : SiteEventIgnores x B) :
-- imply
  TripleEventIgnoresMiddleAt x ((interpolatedSite T) ⁻¹' B) := by
-- proof
  apply StatMech.FrontierA.tripleEventIgnoresMiddleAt_preimage_interpolatedSite T x B hB

/--
[measurableSet_middleThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma measurableSet_middleThreshold_eq
  {d : ℕ}
  {x : Site d}
-- given
  (t : NNReal) :
-- imply
  MeasurableSet {q : FieldTriple d | t ≤ q.2.1 x} := by
-- proof
  apply StatMech.FrontierA.measurableSet_middleThreshold t x

/--
[interpolatedSite_eq_true_of_middleThreshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma interpolatedSite_eq_true_of_middleThreshold_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
  {x : Site d}
-- given
  (h : T.threshold ≤ q.2.1 x) :
-- imply
  interpolatedSite T q x = true := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_eq_true_of_middleThreshold T q x h

/--
[interpolatedSiteLaw_hasInsertionLowerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma interpolatedSiteLaw_hasInsertionLowerBound_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
-- given
  (epsilon : ENNReal)
  (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
-- imply
  HasSiteInsertionLowerBound (interpolatedSiteLaw T mu) epsilon := by
-- proof
  apply StatMech.FrontierA.interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert

/--
[siteInsertion_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma siteInsertion_positive_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  {x : Site d}
  {B : Set (ConfigSpace (Site d))}
-- given
  (epsilon : ENNReal)
  (hepsilon : 0 < epsilon)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hBmeas : MeasurableSet B)
  (hBoff : SiteEventIgnores x B)
  (hBpos : 0 < nu B) :
-- imply
  0 < nu (B ∩ {eta | eta x = true}) := by
-- proof
  apply StatMech.FrontierA.siteInsertion_positive nu epsilon hepsilon hinsert x B hBmeas hBoff hBpos

/--
[forceSiteOccupied_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSiteOccupied_self_eq
  {d : ℕ}
  {x : Site d}
  {eta : ConfigSpace (Site d)} :
-- imply
  forceSiteOccupied x eta x = true := by
-- proof
  apply StatMech.FrontierA.forceSiteOccupied_self x eta

/--
[forceSiteOccupied_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSiteOccupied_apply_of_ne_eq
  {d : ℕ}
  {x y : Site d}
  {eta : ConfigSpace (Site d)}
-- given
  (h : y ≠ x) :
-- imply
  forceSiteOccupied x eta y = eta y := by
-- proof
  apply StatMech.FrontierA.forceSiteOccupied_apply_of_ne h eta

/--
[measurable_forceSiteOccupied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma measurable_forceSiteOccupied_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Measurable (forceSiteOccupied x : ConfigSpace (Site d) → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.FrontierA.measurable_forceSiteOccupied x

/--
[forceSiteOccupied_eq_self_of_eq_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSiteOccupied_eq_self_of_eq_true_eq
  {d : ℕ}
  {x : Site d}
  {eta : ConfigSpace (Site d)}
-- given
  (h : eta x = true) :
-- imply
  forceSiteOccupied x eta = eta := by
-- proof
  apply StatMech.FrontierA.forceSiteOccupied_eq_self_of_eq_true x eta h

/--
[siteEventIgnores_forceSiteOccupied_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma siteEventIgnores_forceSiteOccupied_preimage_eq
  {d : ℕ}
  {x : Site d}
  {B : Set (ConfigSpace (Site d))} :
-- imply
  SiteEventIgnores x ((forceSiteOccupied x) ⁻¹' B) := by
-- proof
  apply StatMech.FrontierA.siteEventIgnores_forceSiteOccupied_preimage x B

/--
[forceSiteOccupied_map_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSiteOccupied_map_absolutelyContinuous_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  {x : Site d}
-- given
  (epsilon : ENNReal)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu.map (forceSiteOccupied x) ≪ nu := by
-- proof
  apply StatMech.FrontierA.forceSiteOccupied_map_absolutelyContinuous nu epsilon hepsilon hinsert x

/--
[forceSitesOccupied_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSitesOccupied_apply_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {eta : ConfigSpace (Site d)}
  {y : Site d} :
-- imply
  forceSitesOccupied S eta y = if y ∈ S then true else eta y := by
-- proof
  apply StatMech.FrontierA.forceSitesOccupied_apply S eta y

/--
[forceSitesOccupied_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSitesOccupied_empty_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  forceSitesOccupied (∅ : Finset (Site d)) eta = eta := by
-- proof
  apply StatMech.FrontierA.forceSitesOccupied_empty eta

/--
[forceSitesOccupied_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSitesOccupied_insert_eq
  {d : ℕ}
  {x : Site d}
  {S : Finset (Site d)} :
-- imply
  (forceSitesOccupied (insert x S) : ConfigSpace (Site d) → ConfigSpace (Site d)) = forceSiteOccupied x ∘ forceSitesOccupied S := by
-- proof
  apply StatMech.FrontierA.forceSitesOccupied_insert x S

/--
[measurable_forceSitesOccupied](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma measurable_forceSitesOccupied_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  Measurable (forceSitesOccupied S : ConfigSpace (Site d) → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.FrontierA.measurable_forceSitesOccupied S

/--
[forceSitesOccupied_map_absolutelyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma forceSitesOccupied_map_absolutelyContinuous_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  {S : Finset (Site d)}
-- given
  (epsilon : ENNReal)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon) :
-- imply
  nu.map (forceSitesOccupied S) ≪ nu := by
-- proof
  apply StatMech.FrontierA.forceSitesOccupied_map_absolutelyContinuous nu epsilon hepsilon hinsert S

/--
[positive_of_forceSitesOccupied_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInsertion.lean)
-/
@[path]
private lemma positive_of_forceSitesOccupied_preimage_eq
  {d : ℕ}
  {nu : Measure (ConfigSpace (Site d))}
  {S : Finset (Site d)}
  {A B : Set (ConfigSpace (Site d))}
-- given
  (epsilon : ENNReal)
  (hepsilon : epsilon ≠ 0)
  (hinsert : HasSiteInsertionLowerBound nu epsilon)
  (hBmeas : MeasurableSet B)
  (hsub : A ⊆ (forceSitesOccupied S) ⁻¹' B)
  (hApos : 0 < nu A) :
-- imply
  0 < nu B := by
-- proof
  apply StatMech.FrontierA.positive_of_forceSitesOccupied_preimage nu epsilon hepsilon hinsert S hBmeas hsub hApos


-- created on 2026-10-23
