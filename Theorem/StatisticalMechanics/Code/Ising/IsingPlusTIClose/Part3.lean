/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part2
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


theorem iti_integral_monomialBcf (T : Finset (Site d)) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] :
    (∫ ω, iti_monomialBcf T ω ∂μ) = μ.real (fmu_multiOpen (E := Site d) T) := by
  have heq : (fun ω => iti_monomialBcf T ω)
      = Set.indicator (fmu_multiOpen (E := Site d) T) (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [iti_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, iti_monomialCM,
      ContinuousMap.prod_apply]
    exact iti_prod_coordCM_eq_indicator T ω
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ)
    (ipe_multiOpen_isClopen T).isClosed.measurableSet]
  simp [Measure.real]


theorem iti_monomialBcf_comp_shift (T : Finset (Site d)) (g : Multiplicative (Site d))
    (ω : ConfigSpace (Site d)) :
    iti_monomialBcf T (shift g ω) = iti_monomialBcf (T.image (fun x => g⁻¹ • x)) ω := by
  simp only [iti_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, iti_monomialCM,
    ContinuousMap.prod_apply]
  rw [iti_prod_coordCM_eq_indicator, iti_prod_coordCM_eq_indicator]
  rw [show (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) (shift g ω)
      = ((shift g) ⁻¹' (fmu_multiOpen (E := Site d) T)).indicator (fun _ => (1:ℝ)) ω from by
    by_cases hm : shift g ω ∈ fmu_multiOpen (E := Site d) T
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show ω ∈ _ from hm)]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show ω ∉ _ from hm)]]
  rw [fmu_shift_multiOpen g T]


theorem iti_decayFun_monomial (μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d)))
    (g : Multiplicative (Site d)) (T : Finset (Site d)) (n : ℕ) :
    pstc_decayFun μ g (iti_monomialBcf T) n
      = ((μ n : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T))
        - ((μ n : Measure (ConfigSpace (Site d))).real
            (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) := by
  unfold pstc_decayFun
  rw [iti_integral_monomialBcf T]
  congr 1
  rw [show (fun ω => iti_monomialBcf T (shift g ω))
      = (fun ω => iti_monomialBcf (T.image (fun x => g⁻¹ • x)) ω) from
        funext (fun ω => iti_monomialBcf_comp_shift T g ω)]
  rw [iti_integral_monomialBcf (T.image (fun x => g⁻¹ • x))]


theorem iti_plus_multiOpen_tendsto (β h : ℝ) (φ : ℕ → ℕ) (T : Finset (Site d))
    (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
    Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T)) atTop
      (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real
        (fmu_multiOpen (E := Site d) T))) :=
  StatMech.WeakConvergesTo.tendsto_real_of_isClopen hconv (ipe_multiOpen_isClopen T)


end Ising
end StatMech
