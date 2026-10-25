/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IntegralShiftDecay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.IVTranslationInvariance.Part2
import Def.StatisticalMechanics.Code.FK.IntegralShiftDecay
open MeasureTheory Filter Topology BoundedContinuousFunction
open StatMech.ConfigSpace StatMech.Lattice


namespace StatMech

namespace FK

variable {d : ℕ}


theorem isd_integral_comp_shift (μ : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    (∫ x, (f.compContinuous ⟨shift g, continuous_shift g⟩) x ∂(μ : Measure _))
      = ∫ x, f (shift g x) ∂(μ : Measure _) := by
  simp only [compContinuous_apply, ContinuousMap.coe_mk]


theorem isd_decayFun_sub_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    |isd_decayFun μ g f n - isd_decayFun μ g f' n| ≤ 2 * ‖f - f'‖ := by
  set T : C(ConfigSpace (Sym2 (Site d)), ConfigSpace (Sym2 (Site d))) :=
    ⟨shift g, continuous_shift g⟩ with hT
  
  let μn : Measure (ConfigSpace (Sym2 (Site d))) := (μ n : Measure _)
  
  have hsub1 : (∫ x, f x ∂μn) - (∫ x, f' x ∂μn) = ∫ x, (f - f') x ∂μn := by
    rw [← integral_sub (f.integrable _) (f'.integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
  
  have hsub2 : (∫ x, f (shift g x) ∂μn) - (∫ x, f' (shift g x) ∂μn)
      = ∫ x, ((f - f').compContinuous T) x ∂μn := by
    rw [show (fun x => f (shift g x)) = (fun x => (f.compContinuous T) x) from rfl,
      show (fun x => f' (shift g x)) = (fun x => (f'.compContinuous T) x) from rfl,
      ← integral_sub ((f.compContinuous T).integrable _) ((f'.compContinuous T).integrable _)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [BoundedContinuousFunction.compContinuous_apply, BoundedContinuousFunction.coe_sub,
      Pi.sub_apply]
  
  have hlin : isd_decayFun μ g f n - isd_decayFun μ g f' n
      = (∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn) := by
    simp only [isd_decayFun]
    rw [← hsub1, ← hsub2]; ring
  rw [hlin]
  
  calc |(∫ x, (f - f') x ∂μn) - (∫ x, ((f - f').compContinuous T) x ∂μn)|
      ≤ |∫ x, (f - f') x ∂μn| + |∫ x, ((f - f').compContinuous T) x ∂μn| := abs_sub _ _
    _ ≤ ‖f - f'‖ + ‖f - f'‖ := by
        gcongr
        · have := (f - f').norm_integral_le_norm μn
          rwa [Real.norm_eq_abs] at this
        · have h1 := ((f - f').compContinuous T).norm_integral_le_norm μn
          have h2 := (f - f').norm_compContinuous_le T
          rw [Real.norm_eq_abs] at h1
          exact h1.trans h2
    _ = 2 * ‖f - f'‖ := by ring


theorem isd_abs_decay_le (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) (f f' : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) (n : ℕ) :
    |isd_decayFun μ g f n| ≤ 2 * ‖f - f'‖ + |isd_decayFun μ g f' n| := by
  have h := isd_decayFun_sub_le μ g f f' n
  have hsplit : |isd_decayFun μ g f n|
      ≤ |isd_decayFun μ g f n - isd_decayFun μ g f' n| + |isd_decayFun μ g f' n| := by
    calc |isd_decayFun μ g f n|
        = |(isd_decayFun μ g f n - isd_decayFun μ g f' n) + isd_decayFun μ g f' n| := by
          ring_nf
      _ ≤ |isd_decayFun μ g f n - isd_decayFun μ g f' n| + |isd_decayFun μ g f' n| :=
          abs_add_le _ _
  linarith [hsplit, h]


theorem isd_tendsto_decay_of_dense (μ : ℕ → ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (g : Multiplicative (Site d)) {D : Set ((ConfigSpace (Sym2 (Site d))) →ᵇ ℝ)}
    (hD : Dense D)
    (hdecay : ∀ f' ∈ D, Tendsto (isd_decayFun μ g f') atTop (𝓝 0))
    (f : (ConfigSpace (Sym2 (Site d))) →ᵇ ℝ) :
    Tendsto (isd_decayFun μ g f) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  
  obtain ⟨f', hf'D, hf'close⟩ := hD.exists_dist_lt f (by positivity : (0:ℝ) < ε / 4)
  have hnorm : ‖f - f'‖ < ε / 4 := by
    rwa [dist_eq_norm] at hf'close
  
  have hf' := hdecay f' hf'D
  rw [Metric.tendsto_atTop] at hf'
  obtain ⟨N, hN⟩ := hf' (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := isd_abs_decay_le μ g f f' n
  have hf'n : |isd_decayFun μ g f' n| < ε / 2 := by
    have := hN n hn
    rwa [Real.dist_eq, sub_zero] at this
  rw [Real.dist_eq, sub_zero]
  calc |isd_decayFun μ g f n|
      ≤ 2 * ‖f - f'‖ + |isd_decayFun μ g f' n| := hbound
    _ < 2 * (ε / 4) + ε / 2 := by gcongr
    _ = ε := by ring


end FK
end StatMech
