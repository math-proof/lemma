/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingBoxSqueeze.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureSurfaceVolume.Part2
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

variable {d : ℕ}


theorem ibs_isClopen_spinUp (x : Site d) :
    IsClopen {ω : ConfigSpace (Site d) | ω x = true} := by
  have h : {ω : ConfigSpace (Site d) | ω x = true} = (fun ω => ω x) ⁻¹' {true} := rfl
  rw [h]
  exact IsClopen.preimage (isClopen_discrete _) (StatMech.ConfigSpace.continuous_eval x)


theorem ibs_measurableSet_spinUp (x : Site d) :
    MeasurableSet {ω : ConfigSpace (Site d) | ω x = true} :=
  (ibs_isClopen_spinUp x).isClosed.measurableSet


theorem ibs_integral_coordBcf (x : Site d) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    (∫ ω, pstc_coordBcf x ω ∂μ) = μ.real {ω | ω x = true} := by
  have heq : (fun ω => pstc_coordBcf x ω)
      = Set.indicator {ω : ConfigSpace (Site d) | ω x = true} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [pstc_coordBcf_apply, Set.indicator]
    by_cases h : ω x <;> simp [h, Set.mem_setOf_eq]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (ibs_measurableSet_spinUp x)]
  simp [Measure.real]


theorem ibs_coordBcf_comp_shift (x : Site d) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Site d)) :
    pstc_coordBcf x (shift g ω) = pstc_coordBcf (g⁻¹ • x) ω := rfl


theorem ibs_decayFun_coord (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (x : Site d) (n : ℕ) :
    pstc_decayFun μ g (pstc_coordBcf x) n
      = ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((μ n : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) := by
  unfold pstc_decayFun
  rw [ibs_integral_coordBcf x]
  congr 1
  rw [show (fun ω => pstc_coordBcf x (shift g ω)) = (fun ω => pstc_coordBcf (g⁻¹ • x) ω) from rfl]
  rw [ibs_integral_coordBcf (g⁻¹ • x)]


theorem ibs_plus_siteProb_tendsto (β h : ℝ) (φ : ℕ → ℕ) (x : Site d)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
    Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        {ω | ω x = true}) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ibs_isClopen_spinUp x)


theorem ibs_minus_siteProb_tendsto (β h : ℝ) (φ : ℕ → ℕ) (x : Site d)
    (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h)) :
    Tendsto (fun n => (minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        {ω | ω x = true}) atTop
      (𝓝 ((minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ibs_isClopen_spinUp x)


theorem ibs_plus_coord_decay_of_density_eq (β h : ℝ) (φ : ℕ → ℕ) (g : Multiplicative (Site d))
    (x : Site d)
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
    (hdens : (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}
      = (plusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
    Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (pstc_coordBcf x))
      atTop (𝓝 0) := by
  have h1 := ibs_plus_siteProb_tendsto β h φ x hconv
  have h2 := ibs_plus_siteProb_tendsto β h φ (g⁻¹ • x) hconv
  have hdecayeq : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (pstc_coordBcf x)
      = fun n => ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            {ω | ω (g⁻¹ • x) = true}) := by
    funext n; exact ibs_decayFun_coord _ g x n
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this


theorem ibs_minus_coord_decay_of_density_eq (β h : ℝ) (φ : ℕ → ℕ) (g : Multiplicative (Site d))
    (x : Site d)
    (hconv : WeakConvergesTo (fun n => minusMeasure d (φ n) β h) (minusState d β h))
    (hdens : (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true}
      = (minusState d β h : Measure (ConfigSpace (Site d))).real {ω | ω (g⁻¹ • x) = true}) :
    Tendsto (pstc_decayFun (fun n => minusMeasure d (φ n) β h) g (pstc_coordBcf x))
      atTop (𝓝 0) := by
  have h1 := ibs_minus_siteProb_tendsto β h φ x hconv
  have h2 := ibs_minus_siteProb_tendsto β h φ (g⁻¹ • x) hconv
  have hdecayeq : pstc_decayFun (fun n => minusMeasure d (φ n) β h) g (pstc_coordBcf x)
      = fun n => ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real {ω | ω x = true})
        - ((minusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
            {ω | ω (g⁻¹ • x) = true}) := by
    funext n; exact ibs_decayFun_coord _ g x n
  rw [hdecayeq]
  have := h1.sub h2
  rw [hdens, sub_self] at this
  exact this


end Ising
end StatMech
