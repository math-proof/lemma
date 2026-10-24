import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSiteTrifurcationZero
open MeasureTheory StatMech StatMech.FrontierA


/--
[measurableSet_siteCanonicalTrifurcationEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma measurableSet_siteCanonicalTrifurcationEvent_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet (SiteCanonicalTrifurcationEvent x) := by
-- proof
  apply StatMech.FrontierA.measurableSet_siteCanonicalTrifurcationEvent x

/--
[siteCanonicalTrifurcation_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcation_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {eta : ConfigSpace (Site d)}
  {x : Site d} :
-- imply
  IsCanonicalTrifurcation d (siteToBond (shift g eta)) (g • x) ↔ IsCanonicalTrifurcation d (siteToBond eta) x := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcation_shift g eta x

/--
[siteCanonicalTrifurcationProb_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcationProb_const_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
  {x : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu (SiteCanonicalTrifurcationEvent x) = mu (SiteCanonicalTrifurcationEvent 0) := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcationProb_const mu hinv x

/--
[siteCanonicalTrifurcationCount_le_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcationCount_le_boundary_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ} :
-- imply
  siteCanonicalTrifurcationCount eta n ≤ boxSV_boundaryCard d (n + 1) := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcationCount_le_boundary eta n

/--
[siteCanonicalTrifurcationCount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcationCount_eq_sum_indicator_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {n : ℕ} :
-- imply
  (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) = ∑ x ∈ boxFinsetBK d n, (SiteCanonicalTrifurcationEvent x).indicator (fun _ ↦ (1 : ℝ≥0∞)) eta := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcationCount_eq_sum_indicator eta n

/--
[expected_siteCanonicalTrifurcationCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma expected_siteCanonicalTrifurcationCount_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  ∫⁻ eta, (siteCanonicalTrifurcationCount eta n : ℝ≥0∞) ∂mu = (boxFinsetBK d n).card • mu (SiteCanonicalTrifurcationEvent 0) := by
-- proof
  apply StatMech.FrontierA.expected_siteCanonicalTrifurcationCount mu hinv n

/--
[siteCanonicalTrifurcation_prob_eq_zero_of_one_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcation_prob_eq_zero_of_one_le_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu (SiteCanonicalTrifurcationEvent 0) = 0 := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcation_prob_eq_zero_of_one_le mu hd hinv

/--
[siteCanonicalTrifurcation_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSiteTrifurcationZero.lean)
-/
@[path]
private lemma siteCanonicalTrifurcation_prob_eq_zero_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure mu]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu {eta | IsCanonicalTrifurcation d (siteToBond eta) 0} = 0 := by
-- proof
  apply StatMech.FrontierA.siteCanonicalTrifurcation_prob_eq_zero mu hinv


-- created on 2026-10-23
