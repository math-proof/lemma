import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.DLRUniqueness
open MeasureTheory Set StatMech StatMech.FK


/--
[ergodic_invariant_event_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_invariant_event_zero_or_one_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  μ s = 0 ∨ μ s = 1 := by
-- proof
  apply StatMech.FK.ergodic_invariant_event_zero_or_one hμ hs hinv

/--
[ergodic_invariant_event_eq_one_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_invariant_event_eq_one_of_pos_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s)
  (hpos : 0 < μ s) :
-- imply
  μ s = 1 := by
-- proof
  apply StatMech.FK.ergodic_invariant_event_eq_one_of_pos hμ hs hinv hpos

/--
[le_self_of_convexCombo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma le_self_of_convexCombo_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  {s : Set (ConfigSpace E)}
-- given
  (hconv : μ = a • ν₁ + b • ν₂) :
-- imply
  a * ν₁ s ≤ μ s ∧ b * ν₂ s ≤ μ s := by
-- proof
  apply StatMech.FK.le_self_of_convexCombo hconv s

/--
[convexSummand_eq_on_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma convexSummand_eq_on_invariants_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hconv : μ = a • ν₁ + b • ν₂)
  (ha : 0 < a)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  ν₁ s = μ s := by
-- proof
  apply StatMech.FK.convexSummand_eq_on_invariants hμ hconv ha hs hinv

/--
[ergodic_eq_on_invariants_of_convexCombo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_eq_on_invariants_of_convexCombo_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hconv : μ = a • ν₁ + b • ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  ν₁ s = μ s ∧ ν₂ s = μ s := by
-- proof
  apply StatMech.FK.ergodic_eq_on_invariants_of_convexCombo hμ hconv ha hb hs hinv

/--
[ergodic_summands_eq_on_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_summands_eq_on_invariants_eq
  [Group G]
  [MulAction G E]
  {μ ν₁ ν₂ : Measure (ConfigSpace E)}
  {a b : ℝ≥0∞}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν₁]
  [IsProbabilityMeasure ν₂]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hconv : μ = a • ν₁ + b • ν₂)
  (ha : 0 < a)
  (hb : 0 < b)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  ν₁ s = ν₂ s := by
-- proof
  apply StatMech.FK.ergodic_summands_eq_on_invariants hμ hconv ha hb hs hinv

/--
[ergodic_invariant_event_zero_or_one_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_invariant_event_zero_or_one_pair_eq
  [Group G]
  [MulAction G E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsErgodic (G := G) μ)
  (hν : IsErgodic (G := G) ν)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  (μ s = 0 ∨ μ s = 1) ∧ (ν s = 0 ∨ ν s = 1) := by
-- proof
  apply StatMech.FK.ergodic_invariant_event_zero_or_one_pair hμ hν hs hinv

/--
[ergodic_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma ergodic_off_countable_eq
  [Group G]
  [MulAction G E]
  {φ : ℝ → Measure (ConfigSpace E)}
  {S : Set ℝ}
-- given
  (hS : S.Countable)
  (herg : ∀ p ∉ S, IsErgodic (G := G) (φ p)) :
-- imply
  {p : ℝ | ¬ IsErgodic (G := G) (φ p)}.Countable := by
-- proof
  apply StatMech.FK.ergodic_off_countable hS herg

/--
[extreme_on_invariants_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DLRUniqueness.lean)
-/
@[path]
private lemma extreme_on_invariants_off_countable_eq
  [Group G]
  [MulAction G E]
  {φ : ℝ → Measure (ConfigSpace E)}
  {S : Set ℝ}
-- given
  (hpm : ∀ p, IsProbabilityMeasure (φ p))
  (herg : ∀ p ∉ S, IsErgodic (G := G) (φ p)) :
-- imply
  ∀ p ∉ S, ∀ (ν₁ ν₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → φ p = a • ν₁ + b • ν₂ → 0 < a → 0 < b → ∀ {s : Set (ConfigSpace E)}, MeasurableSet s → (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) → ν₁ s = ν₂ s := by
-- proof
  apply StatMech.FK.extreme_on_invariants_off_countable hpm herg


-- created on 2026-10-23
