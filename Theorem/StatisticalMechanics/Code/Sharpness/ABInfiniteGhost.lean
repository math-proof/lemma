/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


theorem inhom_real_eq_probV_of_mem {E : Type*} [Fintype E] [DecidableEq E]
    (r : E -> Real) (hr0 : forall e, 0 <= r e)
    (hr1 : forall e, r e <= 1) (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure (fun e => (r e).toNNReal)
      (fun e => Real.toNNReal_le_one.mpr (hr1 e))).real A = probV r A := by
  rw [inhom_real_eq_wprob]
  unfold wprob probV pweight configWeightV edgeWeightV
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : omega e
  · simp only [he, if_true]
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal,
      Real.coe_toNNReal _ (hr0 e)]
  · simp only [he]
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub (Real.toNNReal_le_one.mpr (hr1 e)),
      Real.coe_toNNReal _ (hr0 e)]
    norm_num


theorem inhom_map_cfgEquiv {E : Type*} (p : E -> NNReal)
    (hp : forall e, p e <= 1) (sigma : E ≃ E)
    (hinv : forall e, p (sigma e) = p e) :
    Measure.map (cfgEquiv sigma) (inhomBernoulliProductMeasure p hp) =
      inhomBernoulliProductMeasure p hp := by
  unfold inhomBernoulliProductMeasure
  have hcfg : (cfgEquiv sigma : ConfigSpace E -> ConfigSpace E) =
      (Equiv.piCongrLeft (fun _ : E => Bool) sigma.symm :
        ConfigSpace E -> ConfigSpace E) := by
    funext omega e
    simp only [cfgEquiv_apply, Equiv.piCongrLeft_apply, eq_rec_constant,
      Equiv.symm_symm]
  rw [hcfg]
  have hfamily : (fun e => bernoulliMeasure (p e) (hp e)) =
      (fun e => bernoulliMeasure (p (sigma.symm e)) (hp (sigma.symm e))) := by
    funext e
    exact bernoulliMeasure_congr _ _ (by
      simpa using hinv (sigma.symm e))
  conv_lhs => enter [2]; rw [hfamily]
  simpa only [MeasurableEquiv.coe_piCongrLeft] using
    (Measure.infinitePi_map_piCongrLeft
      (fun e => bernoulliMeasure (p e) (hp e)) sigma.symm)


theorem measurable_cfgEquiv {E F : Type*} (sigma : E ≃ F) :
    Measurable (cfgEquiv sigma : ConfigSpace F -> ConfigSpace E) := by
  have hcfg : (cfgEquiv sigma : ConfigSpace F -> ConfigSpace E) =
      (Equiv.piCongrLeft (fun _ : E => Bool) sigma.symm :
        ConfigSpace F -> ConfigSpace E) := by
    funext omega e
    simp only [cfgEquiv_apply, Equiv.piCongrLeft_apply, eq_rec_constant,
      Equiv.symm_symm]
  rw [hcfg]
  exact (MeasurableEquiv.piCongrLeft (fun _ : E => Bool) sigma.symm).measurable


end Sharpness
end StatMech
