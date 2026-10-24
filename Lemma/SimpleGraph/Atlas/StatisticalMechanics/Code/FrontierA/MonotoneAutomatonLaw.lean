import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw
open MeasureTheory StatMech StatMech.FrontierA


/--
[fieldShift_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma fieldShift_apply_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {xi : NonnegativeField d}
  {x : Site d} :
-- imply
  fieldShift g xi x = xi (g⁻¹ • x) := by
-- proof
  apply StatMech.FrontierA.fieldShift_apply g xi x

/--
[fieldShift_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma fieldShift_one_eq
  {d : ℕ} :
-- imply
  (fieldShift (1 : Multiplicative (Site d)) : NonnegativeField d → NonnegativeField d) = id := by
-- proof
  apply StatMech.FrontierA.fieldShift_one

/--
[fieldShift_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma fieldShift_mul_eq
  {d : ℕ}
-- given
  (g h : Multiplicative (Site d)) :
-- imply
  (fieldShift (g * h) : NonnegativeField d → NonnegativeField d) = fieldShift g ∘ fieldShift h := by
-- proof
  apply StatMech.FrontierA.fieldShift_mul g h

/--
[measurable_fieldShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma measurable_fieldShift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)} :
-- imply
  Measurable (fieldShift g : NonnegativeField d → NonnegativeField d) := by
-- proof
  apply StatMech.FrontierA.measurable_fieldShift g

/--
[raiseField_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma raiseField_self_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {x : Site d}
-- given
  (r : ℝ≥0) :
-- imply
  raiseField xi x r x = max r (xi x) := by
-- proof
  apply StatMech.FrontierA.raiseField_self xi x r

/--
[raiseField_apply_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma raiseField_apply_of_ne_eq
  {d : ℕ}
  {xi : NonnegativeField d}
  {x y : Site d}
-- given
  (h : y ≠ x)
  (r : ℝ≥0) :
-- imply
  raiseField xi x r y = xi y := by
-- proof
  apply StatMech.FrontierA.raiseField_apply_of_ne xi h r

/--
[mem_siteCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma mem_siteCluster_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)}
  {x y : Site d} :
-- imply
  y ∈ siteCluster eta x ↔ (siteOpenGraph eta).Reachable x y := by
-- proof
  apply StatMech.FrontierA.mem_siteCluster

/--
[automatonBondLaw_eq_map_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma automatonBondLaw_eq_map_siteToBond_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (NonnegativeField d)} :
-- imply
  automatonBondLaw T mu = Measure.map siteToBond (automatonSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.automatonBondLaw_eq_map_siteToBond T mu

/--
[automatonSiteLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma automatonSiteLaw_isTranslationInvariant_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (NonnegativeField d)}
-- given
  (hinv : IsFieldTranslationInvariant mu) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (automatonSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.automatonSiteLaw_isTranslationInvariant T mu hinv

/--
[automatonSiteLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma automatonSiteLaw_isErgodic_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (NonnegativeField d)}
-- given
  (herg : IsFieldErgodic mu) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (automatonSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.automatonSiteLaw_isErgodic T mu herg

/--
[automatonBondLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma automatonBondLaw_isTranslationInvariant_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (NonnegativeField d)}
-- given
  (hinv : IsFieldTranslationInvariant mu) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (automatonBondLaw T mu) := by
-- proof
  apply StatMech.FrontierA.automatonBondLaw_isTranslationInvariant T mu hinv

/--
[automatonBondLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonLaw.lean)
-/
@[path]
private lemma automatonBondLaw_isErgodic_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (NonnegativeField d)}
-- given
  (herg : IsFieldErgodic mu) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (automatonBondLaw T mu) := by
-- proof
  apply StatMech.FrontierA.automatonBondLaw_isErgodic T mu herg


-- created on 2026-10-23
