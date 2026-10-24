import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[gsu_plusState_ergodic_extreme_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexUncond.lean)
-/
@[path]
private lemma gsu_plusState_ergodic_extreme_of_decay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → pst_PlusIntegralShiftDecay β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gsu_plusState_ergodic_extreme_of_decay β h hd hβ hh hdecay

/--
[gsu_minusState_ergodic_extreme_of_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexUncond.lean)
-/
@[path]
private lemma gsu_minusState_ergodic_extreme_of_decay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hdecay : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → pst_MinusIntegralShiftDecay β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gsu_minusState_ergodic_extreme_of_decay β h hd hβ hh hdlr hdecay


-- created on 2026-10-23
