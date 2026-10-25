import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[pstc_decayFun_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_decayFun_sub_le_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {f f' : (ConfigSpace (Site d)) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  |pstc_decayFun μ g f n - pstc_decayFun μ g f' n| ≤ 2 * ‖f - f'‖ := by
-- proof
  apply StatMech.Ising.pstc_decayFun_sub_le μ g f f' n

/--
[pstc_abs_decay_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_abs_decay_le_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {f f' : (ConfigSpace (Site d)) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  |pstc_decayFun μ g f n| ≤ 2 * ‖f - f'‖ + |pstc_decayFun μ g f' n| := by
-- proof
  apply StatMech.Ising.pstc_abs_decay_le μ g f f' n

/--
[pstc_tendsto_decay_of_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_tendsto_decay_of_dense_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {D : Set ((ConfigSpace (Site d)) →ᵇ ℝ)}
  {f : (ConfigSpace (Site d)) →ᵇ ℝ}
-- given
  (hD : Dense D)
  (hdecay : ∀ f' ∈ D, Tendsto (pstc_decayFun μ g f') atTop (𝓝 0)) :
-- imply
  Tendsto (pstc_decayFun μ g f) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.pstc_tendsto_decay_of_dense μ g hD hdecay f

/--
[pstc_coordCM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_coordCM_apply_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Site d)} :
-- imply
  pstc_coordCM x ω = if ω x then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.Ising.pstc_coordCM_apply x ω

/--
[pstc_coordBcf_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_coordBcf_apply_eq
  {d : ℕ}
  {x : Site d}
  {ω : ConfigSpace (Site d)} :
-- imply
  pstc_coordBcf x ω = if ω x then (1 : ℝ) else 0 := by
-- proof
  apply StatMech.Ising.pstc_coordBcf_apply x ω

/--
[pstc_cylinderAlg_separatesPoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_cylinderAlg_separatesPoints_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  (pstc_cylinderAlg d).SeparatesPoints := by
-- proof
  apply StatMech.Ising.pstc_cylinderAlg_separatesPoints d

/--
[pstc_cylinderBcfSet_dense](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_cylinderBcfSet_dense_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  Dense (pstc_cylinderBcfSet d) := by
-- proof
  apply StatMech.Ising.pstc_cylinderBcfSet_dense d

/--
[pstc_decayFun_plus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_decayFun_plus_eq_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ) :
-- imply
  pstc_decayFun (fun n => plusMeasure d (φ n) β h) g f = fun n => (∫ x, f x ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) - (∫ x, f (shift g x) ∂((plusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := by
-- proof
  apply StatMech.Ising.pstc_decayFun_plus_eq β h g φ f

/--
[pstc_decayFun_minus_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_decayFun_minus_eq_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ) :
-- imply
  pstc_decayFun (fun n => minusMeasure d (φ n) β h) g f = fun n => (∫ x, f x ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) - (∫ x, f (shift g x) ∂((minusMeasure d (φ n) β h : ProbabilityMeasure _) : Measure _)) := by
-- proof
  apply StatMech.Ising.pstc_decayFun_minus_eq β h g φ f

/--
[pstc_plusIntegralShiftDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_plusIntegralShiftDecay_of_cylinderDecay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hcyl : pstc_PlusCylinderDecay β h g φ) :
-- imply
  pst_PlusIntegralShiftDecay β h g φ := by
-- proof
  apply StatMech.Ising.pstc_plusIntegralShiftDecay_of_cylinderDecay β h g φ hcyl

/--
[pstc_minusIntegralShiftDecay_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_minusIntegralShiftDecay_of_cylinderDecay_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hcyl : pstc_MinusCylinderDecay β h g φ) :
-- imply
  pst_MinusIntegralShiftDecay β h g φ := by
-- proof
  apply StatMech.Ising.pstc_minusIntegralShiftDecay_of_cylinderDecay β h g φ hcyl

/--
[pstc_decayFun_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_decayFun_one_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {f : (ConfigSpace (Site d)) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  pstc_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
-- proof
  apply StatMech.Ising.pstc_decayFun_one μ f n

/--
[pstc_plusCylinderDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_plusCylinderDecay_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.pstc_plusCylinderDecay_one β h φ

/--
[pstc_minusCylinderDecay_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_minusCylinderDecay_one_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ) :
-- imply
  pstc_MinusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
-- proof
  apply StatMech.Ising.pstc_minusCylinderDecay_one β h φ

/--
[pstc_plusState_isTranslationInvariant_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_plusState_isTranslationInvariant_of_cylinderDecay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → pstc_PlusCylinderDecay β h g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pstc_plusState_isTranslationInvariant_of_cylinderDecay β h hcyl

/--
[pstc_minusState_isTranslationInvariant_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_minusState_isTranslationInvariant_of_cylinderDecay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → pstc_MinusCylinderDecay β h g φ) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pstc_minusState_isTranslationInvariant_of_cylinderDecay β h hcyl

/--
[pstc_plusState_ergodic_extreme_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_plusState_ergodic_extreme_of_cylinderDecay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) → pstc_PlusCylinderDecay β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pstc_plusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh hcyl

/--
[pstc_minusState_ergodic_extreme_of_cylinderDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean)
-/
@[path]
private lemma pstc_minusState_ergodic_extreme_of_cylinderDecay_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
  (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ → WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) → pstc_MinusCylinderDecay β h g φ) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d))) ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.pstc_minusState_ergodic_extreme_of_cylinderDecay β h hd hβ hh hdlr hcyl


-- created on 2026-10-23
