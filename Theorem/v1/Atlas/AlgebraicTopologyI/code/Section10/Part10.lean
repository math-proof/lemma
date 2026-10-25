/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part22
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace BrouwerFixedPoint

open Metric Set Inner

variable {X : Type u} [TopologicalSpace X]

/-- The raw suspension `suspRaw n f` preserves the unit sphere: if `‖v‖ = 1` then
`‖suspRaw n f v‖ = 1`. This is what makes `suspRaw` descend to a well-defined map
`S^{n+1} → S^{n+1}`. -/
lemma suspRaw_norm (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n)
    (v : EuclideanSpace ℝ (Fin (n + 2))) (hv : ‖v‖ = 1) :
    ‖suspRaw n f v‖ = 1 := by
  have sph_norm_fact : ‖(f.1 (suspSafeNorm n (suspInitProj n v))).val‖ = 1 := by
    have := (f.1 (suspSafeNorm n (suspInitProj n v))).property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have snoc_norm : ‖suspRaw n f v‖ ^ 2 =
      ‖(‖suspInitProj n v‖ • (f.1 (suspSafeNorm n (suspInitProj n v))).val)‖ ^ 2 +
      (v (Fin.last (n + 1))) ^ 2 := by
    simp [suspRaw, EuclideanSpace.real_norm_sq_eq, suspSnocProj, Fin.sum_univ_castSucc,
          Fin.snoc_castSucc, Fin.snoc_last]
  rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), sph_norm_fact, mul_one] at snoc_norm
  have norm_decomp : 1 = ‖suspInitProj n v‖ ^ 2 + (v (Fin.last (n + 1))) ^ 2 := by
    have := congr_arg (· ^ 2) hv; simp only [one_pow] at this; rw [← this]
    simp [EuclideanSpace.real_norm_sq_eq, suspInitProj, Fin.sum_univ_castSucc]
  nlinarith [norm_nonneg (suspRaw n f v), sq_nonneg (‖suspRaw n f v‖ - 1),
             snoc_norm.trans norm_decomp.symm]

/-- Away from zero, the safe normalization map is given by the expected formula
`w ↦ w / ‖w‖`. -/
lemma suspSafeNorm_val_of_ne_zero (n : ℕ) (w : EuclideanSpace ℝ (Fin (n + 1)))
    (hw : w ≠ 0) : (suspSafeNorm n w).val = ‖w‖⁻¹ • w := by
  simp [suspSafeNorm, hw]

/-- Continuity of the raw suspension `suspRaw n f`. The only non-trivial point is `w = 0`
in the first `n+1` coordinates, where the radial normalization is squeezed to `0` by the
boundedness `‖f(·)‖ = 1`. -/
lemma continuous_suspRaw (n : ℕ) (f : sphereTopCat n ⟶ sphereTopCat n) :
    Continuous (suspRaw n f) := by
  unfold suspRaw suspSnocProj
  apply (EuclideanSpace.equiv _ _).symm.continuous.comp
  apply continuous_pi; intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Fin.snoc_last]
    exact (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last (n + 1))).continuous
  · intro j; simp only [Fin.snoc_castSucc]
    have h_init_cont : Continuous (suspInitProj n) := by
      apply (EuclideanSpace.equiv _ _).symm.continuous.comp
      exact continuous_pi (fun i => (EuclideanSpace.proj (𝕜 := ℝ) (Fin.castSucc i)).continuous)
    have h_core : Continuous (fun w : EuclideanSpace ℝ (Fin (n + 1)) =>
        ‖w‖ • (f.1 (suspSafeNorm n w)).val) := by
      rw [continuous_iff_continuousAt]; intro w; by_cases hw : w = 0
      · subst hw
        change Filter.Tendsto _ (nhds 0)
          (nhds (‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ • _))
        simp only [norm_zero, zero_smul]
        apply squeeze_zero_norm
          (f := fun x => ‖x‖ • (f.1 (suspSafeNorm n x)).val)
        · intro x
          have : ‖(f.1 (suspSafeNorm n x)).val‖ = 1 := by
            have := (f.1 (suspSafeNorm n x)).property
            rwa [Metric.mem_sphere, dist_zero_right] at this
          rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), this, mul_one]
        · simpa [norm_zero] using
            continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin (n + 1)))
      · apply ContinuousAt.smul continuous_norm.continuousAt
        have h_sNorm_at : ContinuousAt (suspSafeNorm n) w := by
          have hval : ContinuousAt (fun x => (suspSafeNorm n x).val) w :=
            (ContinuousAt.smul
              (ContinuousAt.inv₀ continuous_norm.continuousAt (norm_ne_zero_iff.mpr hw))
              continuousAt_id).congr
              (Filter.eventually_of_mem (isOpen_ne.mem_nhds hw)
                (fun x hx => (suspSafeNorm_val_of_ne_zero n x hx).symm))
          rw [ContinuousAt] at hval ⊢
          change Filter.Tendsto (suspSafeNorm n) (nhds w)
            (@nhds (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) _ _)
          rw [nhds_subtype]
          exact Filter.tendsto_comap_iff.mpr hval

        exact (continuous_subtype_val.comp f.1.continuous).continuousAt.comp h_sNorm_at
    exact ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (h_core.comp h_init_cont))

end BrouwerFixedPoint
