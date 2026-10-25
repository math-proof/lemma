import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation.Part3
open MeasureTheory StatMech StatMech.FrontierA


/--
[tripleFieldShift_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma tripleFieldShift_fst_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {q : FieldTriple d} :
-- imply
  (tripleFieldShift g q).1 = fieldShift g q.1 := by
-- proof
  apply StatMech.FrontierA.tripleFieldShift_fst g q

/--
[tripleFieldShift_snd_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma tripleFieldShift_snd_fst_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {q : FieldTriple d} :
-- imply
  (tripleFieldShift g q).2.1 = fieldShift g q.2.1 := by
-- proof
  apply StatMech.FrontierA.tripleFieldShift_snd_fst g q

/--
[tripleFieldShift_snd_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma tripleFieldShift_snd_snd_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {q : FieldTriple d} :
-- imply
  (tripleFieldShift g q).2.2 = fieldShift g q.2.2 := by
-- proof
  apply StatMech.FrontierA.tripleFieldShift_snd_snd g q

/--
[tripleFieldShift_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma tripleFieldShift_one_eq
  {d : ℕ} :
-- imply
  (tripleFieldShift (1 : Multiplicative (Site d)) : FieldTriple d → FieldTriple d) = id := by
-- proof
  apply StatMech.FrontierA.tripleFieldShift_one

/--
[tripleFieldShift_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma tripleFieldShift_mul_eq
  {d : ℕ}
-- given
  (g h : Multiplicative (Site d)) :
-- imply
  (tripleFieldShift (g * h) : FieldTriple d → FieldTriple d) = tripleFieldShift g ∘ tripleFieldShift h := by
-- proof
  apply StatMech.FrontierA.tripleFieldShift_mul g h

/--
[measurable_tripleFieldShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma measurable_tripleFieldShift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)} :
-- imply
  Measurable (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
-- proof
  apply StatMech.FrontierA.measurable_tripleFieldShift g

/--
[interpolatedSite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedSite_apply_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
  {x : Site d} :
-- imply
  interpolatedSite T q x = (T q.1 x || decide (T.threshold ≤ q.2.1 x)) := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_apply T q x

/--
[measurable_interpolatedSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma measurable_interpolatedSite_eq
  {d : ℕ}
  {T : MonotoneAutomaton d} :
-- imply
  Measurable (interpolatedSite T : FieldTriple d → ConfigSpace (Site d)) := by
-- proof
  apply StatMech.FrontierA.measurable_interpolatedSite T

/--
[interpolatedSite_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedSite_shift_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {g : Multiplicative (Site d)}
  {q : FieldTriple d} :
-- imply
  interpolatedSite T (tripleFieldShift g q) = shift g (interpolatedSite T q) := by
-- proof
  apply StatMech.FrontierA.interpolatedSite_shift T g q

/--
[automatonLow_le_interpolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma automatonLow_le_interpolated_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d} :
-- imply
  T q.1 ≤ interpolatedSite T q := by
-- proof
  apply StatMech.FrontierA.automatonLow_le_interpolated T q

/--
[interpolated_le_automatonMiddle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolated_le_automatonMiddle_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
-- given
  (hq : IsMonotoneFieldTriple q) :
-- imply
  interpolatedSite T q ≤ T q.2.1 := by
-- proof
  apply StatMech.FrontierA.interpolated_le_automatonMiddle T q hq

/--
[automatonMiddle_le_automatonHigh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma automatonMiddle_le_automatonHigh_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
-- given
  (hq : IsMonotoneFieldTriple q) :
-- imply
  T q.2.1 ≤ T q.2.2 := by
-- proof
  apply StatMech.FrontierA.automatonMiddle_le_automatonHigh T q hq

/--
[monotoneAutomaton_interpolation_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma monotoneAutomaton_interpolation_sandwich_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {q : FieldTriple d}
-- given
  (hq : IsMonotoneFieldTriple q) :
-- imply
  T q.1 ≤ interpolatedSite T q ∧ interpolatedSite T q ≤ T q.2.1 ∧ T q.2.1 ≤ T q.2.2 := by
-- proof
  apply StatMech.FrontierA.monotoneAutomaton_interpolation_sandwich T q hq

/--
[interpolatedBondLaw_eq_map_siteToBond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedBondLaw_eq_map_siteToBond_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)} :
-- imply
  interpolatedBondLaw T mu = Measure.map siteToBond (interpolatedSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.interpolatedBondLaw_eq_map_siteToBond T mu

/--
[interpolatedSiteLaw_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedSiteLaw_isTranslationInvariant_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
-- given
  (hinv : IsTripleFieldTranslationInvariant mu) :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (interpolatedSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.interpolatedSiteLaw_isTranslationInvariant T mu hinv

/--
[interpolatedSiteLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedSiteLaw_isErgodic_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
-- given
  (herg : IsTripleFieldErgodic mu) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (interpolatedSiteLaw T mu) := by
-- proof
  apply StatMech.FrontierA.interpolatedSiteLaw_isErgodic T mu herg

/--
[interpolatedBondLaw_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean)
-/
@[path]
private lemma interpolatedBondLaw_isErgodic_eq
  {d : ℕ}
  {T : MonotoneAutomaton d}
  {mu : Measure (FieldTriple d)}
-- given
  (herg : IsTripleFieldErgodic mu) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (interpolatedBondLaw T mu) := by
-- proof
  apply StatMech.FrontierA.interpolatedBondLaw_isErgodic T mu herg


-- created on 2026-10-23
