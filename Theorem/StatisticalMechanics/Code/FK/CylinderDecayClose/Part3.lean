/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CylinderDecayClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IntegralDecayClose.Part5
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.FK.CylinderDecayClose.Part2
open MeasureTheory Filter Topology BoundedContinuousFunction SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


@[simp] theorem cdc_monomialCM_apply (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialCM s ω = ∏ e ∈ s, idc_coordCM e ω := by
  simp only [cdc_monomialCM, ContinuousMap.prod_apply]

@[simp] theorem cdc_monomialBcf_apply (s : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialBcf s ω = ∏ e ∈ s, idc_coordCM e ω := by
  simp only [cdc_monomialBcf, BoundedContinuousFunction.mkOfCompact_apply, cdc_monomialCM_apply]


theorem cdc_integral_monomialBcf (s : Finset (Sym2 (Site d)))
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsFiniteMeasure μ] :
    (∫ ω, cdc_monomialBcf s ω ∂μ) = μ.real (cdc_multiOpenEvent s) := by
  have heq : (fun ω => cdc_monomialBcf s ω)
      = Set.indicator (cdc_multiOpenEvent s) (fun _ => (1 : ℝ)) := by
    funext ω
    rw [cdc_monomialBcf_apply, cdc_prod_coordCM_eq_indicator]
  rw [heq, MeasureTheory.integral_indicator_const (1 : ℝ) (cdc_multiOpenEvent_measurable s)]
  simp


theorem cdc_monomialBcf_comp_shift (s : Finset (Sym2 (Site d)))
    (g : Multiplicative (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    cdc_monomialBcf s (shift g ω)
      = (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))).indicator (fun _ => (1:ℝ)) ω := by
  rw [cdc_monomialBcf_apply]
  have : (∏ e ∈ s, idc_coordCM e (shift g ω))
      = (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))).indicator (fun _ => (1:ℝ)) ω := by
    rw [← cdc_prod_coordCM_eq_indicator]
    rw [Finset.prod_image (fun a _ b _ hab => by
      have : g⁻¹ • a = g⁻¹ • b := hab
      exact (MulAction.injective g⁻¹) this)]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [idc_coordCM_apply, idc_coordCM_apply, shift_apply]
  exact this


theorem cdc_decayFun_monomial (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))) (n : ℕ) :
    isd_decayFun μ g (cdc_monomialBcf s) n
      = ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real (cdc_multiOpenEvent s))
        - ((μ n : Measure (ConfigSpace (Sym2 (Site d)))).real
            (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e)))) := by
  unfold isd_decayFun
  rw [cdc_integral_monomialBcf s]
  congr 1
  
  have hshift : (fun ω => cdc_monomialBcf s (shift g ω))
      = Set.indicator (cdc_multiOpenEvent (s.image (fun e => g⁻¹ • e))) (fun _ => (1:ℝ)) := by
    funext ω; exact cdc_monomialBcf_comp_shift s g ω
  rw [hshift,
    MeasureTheory.integral_indicator_const (1 : ℝ)
      (cdc_multiOpenEvent_measurable (s.image (fun e => g⁻¹ • e)))]
  simp


end FK
end StatMech
