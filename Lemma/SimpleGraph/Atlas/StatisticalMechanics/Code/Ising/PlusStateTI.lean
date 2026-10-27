import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[pst_integral_plusShifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_integral_plusShifted_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {n : ℕ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ) :
-- imply
  (∫ x, f x ∂((pst_plusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _)) = ∫ x, f (shift g x) ∂((plusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
-- proof
  apply StatMech.Ising.pst_integral_plusShifted β h g n f

/--
[pst_integral_minusShifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_integral_minusShifted_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {n : ℕ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ) :
-- imply
  (∫ x, f x ∂((pst_minusShiftedFinite β h g n : ProbabilityMeasure _) : Measure _)) = ∫ x, f (shift g x) ∂((minusMeasure d n β h : ProbabilityMeasure _) : Measure _) := by
-- proof
  apply StatMech.Ising.pst_integral_minusShifted β h g n f

/--
[pst_plusShifted_weakConverges_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_plusShifted_weakConverges_of_decay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hdecay : pst_PlusIntegralShiftDecay β h g φ) :
-- imply
  WeakConvergesTo (fun n => pst_plusShiftedFinite β h g (φ n)) (plusState d β h) := by
-- proof
  apply StatMech.Ising.pst_plusShifted_weakConverges_of_decay β h g φ hconv hdecay

/--
[pst_minusShifted_weakConverges_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_minusShifted_weakConverges_of_decay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h))
  (hdecay : pst_MinusIntegralShiftDecay β h g φ) :
-- imply
  WeakConvergesTo (fun n => pst_minusShiftedFinite β h g (φ n)) (minusState d β h) := by
-- proof
  apply StatMech.Ising.pst_minusShifted_weakConverges_of_decay β h g φ hconv hdecay

/--
[pst_plusState_map_shift_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_plusState_map_shift_of_decay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
-- given
  (β h : ℝ)
  (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → pst_PlusIntegralShiftDecay β h g φ) :
-- imply
  Measure.map (shift g) (plusState d β h : Measure (ConfigSpace (Site d))) = (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pst_plusState_map_shift_of_decay β h g hdecay

/--
[pst_minusState_map_shift_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_minusState_map_shift_of_decay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
-- given
  (β h : ℝ)
  (hdecay : ∀ φ : ℕ → ℕ, StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → pst_MinusIntegralShiftDecay β h g φ) :
-- imply
  Measure.map (shift g) (minusState d β h : Measure (ConfigSpace (Site d))) = (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pst_minusState_map_shift_of_decay β h g hdecay

/--
[pst_plusState_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_plusState_isTranslationInvariant_of_decay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → pst_PlusIntegralShiftDecay β h g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pst_plusState_isTranslationInvariant_of_decay β h hdecay

/--
[pst_minusState_isTranslationInvariant_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_minusState_isTranslationInvariant_of_decay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → pst_MinusIntegralShiftDecay β h g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pst_minusState_isTranslationInvariant_of_decay β h hdecay

/--
[pst_plusIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_plusIntegralShiftDecay_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  pst_PlusIntegralShiftDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.pst_plusIntegralShiftDecay_one β h φ

/--
[pst_minusIntegralShiftDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTI.lean)
-/
@[path]
private lemma pst_minusIntegralShiftDecay_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  pst_MinusIntegralShiftDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.pst_minusIntegralShiftDecay_one β h φ


-- created on 2026-10-23
