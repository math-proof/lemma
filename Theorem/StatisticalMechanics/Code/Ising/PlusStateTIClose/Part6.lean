/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTI.Part2
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexUncond
import Def.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem pstc_plusIntegralShiftDecay_of_cylinderDecay (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hcyl : pstc_PlusCylinderDecay β h g φ) :
    pst_PlusIntegralShiftDecay β h g φ := by
  intro f
  have h := pstc_tendsto_decay_of_dense (fun n => plusMeasure d (φ n) β h) g
    (pstc_cylinderBcfSet_dense d) hcyl f
  rw [pstc_decayFun_plus_eq] at h
  exact h


theorem pstc_minusIntegralShiftDecay_of_cylinderDecay (β h : ℝ) (g : Multiplicative (Site d))
    (φ : ℕ → ℕ) (hcyl : pstc_MinusCylinderDecay β h g φ) :
    pst_MinusIntegralShiftDecay β h g φ := by
  intro f
  have h := pstc_tendsto_decay_of_dense (fun n => minusMeasure d (φ n) β h) g
    (pstc_cylinderBcfSet_dense d) hcyl f
  rw [pstc_decayFun_minus_eq] at h
  exact h


theorem pstc_decayFun_one (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (f : (ConfigSpace (Site d)) →ᵇ ℝ) (n : ℕ) :
    pstc_decayFun μ (1 : Multiplicative (Site d)) f n = 0 := by
  simp only [pstc_decayFun, shift_one, id_eq, sub_self]


theorem pstc_plusCylinderDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pstc_PlusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : pstc_decayFun (fun n => plusMeasure d (φ n) β h)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact pstc_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds


theorem pstc_minusCylinderDecay_one (β h : ℝ) (φ : ℕ → ℕ) :
    pstc_MinusCylinderDecay β h (1 : Multiplicative (Site d)) φ := by
  intro f _
  have hzero : pstc_decayFun (fun n => minusMeasure d (φ n) β h)
      (1 : Multiplicative (Site d)) f = fun _ => (0 : ℝ) := by
    funext n; exact pstc_decayFun_one _ f n
  rw [hzero]
  exact tendsto_const_nhds


theorem pstc_plusState_isTranslationInvariant_of_cylinderDecay (β h : ℝ)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pstc_PlusCylinderDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) :=
  pst_plusState_isTranslationInvariant_of_decay β h
    (fun g φ hφ hconv => pstc_plusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))


theorem pstc_minusState_isTranslationInvariant_of_cylinderDecay (β h : ℝ)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pstc_MinusCylinderDecay β h g φ) :
    ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) :=
  pst_minusState_isTranslationInvariant_of_decay β h
    (fun g φ hφ hconv => pstc_minusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))


theorem pstc_plusState_ergodic_extreme_of_cylinderDecay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h) →
        pstc_PlusCylinderDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (plusState d β h : Measure (ConfigSpace (Site d))) :=
  gsu_plusState_ergodic_extreme_of_decay β h hd hβ hh
    (fun g φ hφ hconv => pstc_plusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))


theorem pstc_minusState_ergodic_extreme_of_cylinderDecay (β h : ℝ)
    (hd : 1 ≤ d) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hdlr : IsDLRState d β h (minusState d β h : Measure (ConfigSpace (Site d))))
    (hcyl : ∀ (g : Multiplicative (Site d)) (φ : ℕ → ℕ), StrictMono φ →
        WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h) →
        pstc_MinusCylinderDecay β h g φ) :
    IsErgodic (G := Multiplicative (Site d)) (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ IsDLRExtremePoint β h (minusState d β h : Measure (ConfigSpace (Site d))) :=
  gsu_minusState_ergodic_extreme_of_decay β h hd hβ hh hdlr
    (fun g φ hφ hconv => pstc_minusIntegralShiftDecay_of_cylinderDecay β h g φ (hcyl g φ hφ hconv))

end Ising
end StatMech
