/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CauchyKernelIntegrability
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

open scoped SchwartzMap
open MvPolynomial MeasureTheory ContinuousLinearMap Filter Asymptotics

noncomputable section

namespace DifferentialOperators

/-- The Cauchy-Riemann polynomial `X₀ + i·X₁`, whose associated constant-coefficient differential
operator is the Cauchy-Riemann (`∂̄`) operator on `ℝ² ≅ ℂ`. -/
def dbarPoly : MvPolynomial (Fin 2) ℂ :=
  X 0 + C Complex.I * X 1

/-- The Cauchy-Riemann (`∂̄`) operator on tempered distributions on `ℝ²`, defined as the
constant-coefficient differential operator with symbol `dbarPoly`. -/
def dbarOp : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  constCoeffDiffOp 2 dbarPoly

/-- The Cauchy-Riemann kernel `(2π)⁻¹·(x + iy)⁻¹` on `ℝ²`: this is the (distributional) fundamental
solution of the Cauchy-Riemann operator `∂̄`. -/
def cauchyRiemannKernel : EuclideanSpace ℝ (Fin 2) → ℂ :=
  fun v => ((2 * Real.pi : ℝ) : ℂ)⁻¹ * ((v 0 : ℂ) + Complex.I * (v 1 : ℂ))⁻¹


/-- The measurable equivalence between `EuclideanSpace ℝ (Fin 2)` (with the L² product
structure) and `ℝ × ℝ`. -/
noncomputable def euclidProdMeasurableEquiv : EuclideanSpace ℝ (Fin 2) ≃ᵐ (ℝ × ℝ) where
  toEquiv := (WithLp.equiv 2 (Fin 2 → ℝ)).trans (piFinTwoEquiv fun _ => ℝ)
  measurable_toFun := by
    show Measurable (fun v : EuclideanSpace ℝ (Fin 2) => (v 0, v 1)); fun_prop
  measurable_invFun := Continuous.measurable
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
      (continuous_pi (fun i => by fin_cases i <;> continuity)))

set_option maxHeartbeats 1600000 in
/-- The Cauchy-Riemann kernel is locally integrable with respect to Lebesgue measure on `ℝ²`. -/
theorem cauchyRiemannKernel_locallyIntegrable :
    LocallyIntegrable cauchyRiemannKernel
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
  set T := euclidProdMeasurableEquiv
  have hfun : cauchyRiemannKernel = fun v =>
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * CauchyKernel.cauchyKernelBare (T v) := by
    ext v; simp only [cauchyRiemannKernel, CauchyKernel.cauchyKernelBare, T,
      euclidProdMeasurableEquiv]; rfl
  rw [hfun]
  show LocallyIntegrable (((2 * Real.pi : ℝ) : ℂ)⁻¹ •
    (CauchyKernel.cauchyKernelBare ∘ T)) volume
  apply LocallyIntegrable.smul _ ((2 * Real.pi : ℝ) : ℂ)⁻¹
  have hmp : MeasurePreserving T volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  have hTcont : Continuous T := by
    show Continuous (fun v : EuclideanSpace ℝ (Fin 2) => (v 0, v 1)); fun_prop
  rw [locallyIntegrable_iff]
  intro K hK
  have h := CauchyKernel.cauchyKernelBare_locallyIntegrable.integrableOn_isCompact
    (hK.image hTcont)
  have key := (hmp.integrableOn_comp_preimage T.measurableEmbedding (s := T '' K)).mpr h
  rwa [Set.preimage_image_eq K T.injective] at key

/-- The norm of the complex number `x + iy` agrees with the Euclidean norm of the vector
`(x, y)` in `EuclideanSpace ℝ (Fin 2)`. -/
lemma complex_norm_eq_euclidean_norm (v : EuclideanSpace ℝ (Fin 2)) :
    ‖((v 0 : ℂ) + Complex.I * (v 1 : ℂ))‖ = ‖v‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hre : ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)).re = v 0 := by simp
  have him : ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)).im = v 1 := by simp
  rw [hre, him, EuclideanSpace.norm_eq]
  congr 1; simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- For `‖v‖ ≥ 1`, the Cauchy-Riemann kernel is bounded in norm by `(2π)⁻¹`. -/
lemma cauchyRiemannKernel_norm_le (v : EuclideanSpace ℝ (Fin 2)) (hv : 1 ≤ ‖v‖) :
    ‖cauchyRiemannKernel v‖ ≤ (2 * Real.pi)⁻¹ := by
  simp only [cauchyRiemannKernel, norm_mul, norm_inv, Complex.norm_real,
    complex_norm_eq_euclidean_norm]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2), Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  calc (2 * Real.pi)⁻¹ * ‖v‖⁻¹ ≤ (2 * Real.pi)⁻¹ * 1 := by
        gcongr; exact inv_le_one_of_one_le₀ hv
      _ = _ := mul_one _


/-- The product of a Schwartz function with the Cauchy-Riemann kernel is Lebesgue integrable
on `ℝ²`. -/
theorem cauchyRiemannKernel_schwartz_integrable
    (φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) :
    Integrable (fun v => φ v • cauchyRiemannKernel v) volume := by

  have hloc : LocallyIntegrable (fun v => φ v • cauchyRiemannKernel v) volume := by
    intro x
    obtain ⟨K, hK_mem, hK_int⟩ := cauchyRiemannKernel_locallyIntegrable x
    obtain ⟨r, hr, hrK⟩ := Metric.mem_nhds_iff.mp hK_mem
    refine ⟨Metric.closedBall x (r/2), Metric.closedBall_mem_nhds x (by linarith), ?_⟩
    have hcompact := isCompact_closedBall x (r/2)
    obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn φ.continuous.continuousOn
    have hK_ball : IntegrableOn cauchyRiemannKernel (Metric.closedBall x (r/2)) volume :=
      hK_int.mono (fun v hv => hrK (Metric.closedBall_subset_ball (by linarith) hv)) le_rfl
    exact hK_ball.bdd_smul C (φ.continuous.aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_closedBall (fun v hv => hC v hv))

  have hbigO : (fun v => φ v • cauchyRiemannKernel v) =O[cocompact _] (fun v => φ v) := by
    rw [isBigO_iff]
    refine ⟨(2 * Real.pi)⁻¹, ?_⟩
    rw [hasBasis_cocompact.eventually_iff]
    refine ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, fun v hv => ?_⟩
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hv
    rw [norm_smul]
    have hv' : 1 ≤ ‖v‖ := by linarith
    calc ‖φ v‖ * ‖cauchyRiemannKernel v‖
        ≤ ‖φ v‖ * (2 * Real.pi)⁻¹ := by gcongr; exact cauchyRiemannKernel_norm_le v hv'
      _ = (2 * Real.pi)⁻¹ * ‖φ v‖ := by ring

  have hφ_int : IntegrableAtFilter (fun v => φ v) (cocompact _) volume :=
    φ.integrable.integrableAtFilter _

  exact hloc.integrable_of_isBigO_cocompact hbigO hφ_int


set_option maxHeartbeats 3200000 in
/-- Continuity estimate for the Cauchy-Riemann functional: there exist a finite set `s` of
Schwartz seminorm indices and a nonnegative constant `C` such that for every Schwartz function
`φ` the integral `∫ φ v • cauchyRiemannKernel v` is bounded by `C · sup of seminorms in `s`. This
provides the continuity needed to define the Cauchy-Riemann tempered distribution. -/
theorem cauchyRiemannKernel_integral_bound :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)),
        ‖∫ v, φ v • cauchyRiemannKernel v‖ ≤
          C * (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2)) ℂ)) φ := by

  set μ : Measure (EuclideanSpace ℝ (Fin 2)) := volume
  set p := μ.integrablePower

  set s := Finset.Iic ((p, 0) : ℕ × ℕ)
  set SF := schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin 2)) ℂ


  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  have hBmeas : MeasurableSet B := measurableSet_closedBall

  have hE_intOn : IntegrableOn cauchyRiemannKernel B μ :=
    cauchyRiemannKernel_locallyIntegrable.integrableOn_isCompact (isCompact_closedBall 0 1)
  set A := ∫ v in B, ‖cauchyRiemannKernel v‖ ∂μ

  set B' := 2 ^ p * ∫ x : EuclideanSpace ℝ (Fin 2), (1 + ‖x‖) ^ (-(p : ℝ)) ∂μ

  set C := A + (2 * Real.pi)⁻¹ * B' * 2
  use s, C
  constructor
  ·
    apply add_nonneg
    · exact integral_nonneg (fun v => norm_nonneg _)
    · positivity
  ·
    intro φ

    have hint : Integrable (fun v => φ v • cauchyRiemannKernel v) μ :=
      cauchyRiemannKernel_schwartz_integrable φ

    have hsplit := integral_add_compl hBmeas hint
    rw [← hsplit]

    calc ‖∫ v in B, φ v • cauchyRiemannKernel v ∂μ +
            ∫ v in Bᶜ, φ v • cauchyRiemannKernel v ∂μ‖
        ≤ ‖∫ v in B, φ v • cauchyRiemannKernel v ∂μ‖ +
            ‖∫ v in Bᶜ, φ v • cauchyRiemannKernel v ∂μ‖ := norm_add_le _ _
      _ ≤ A * (s.sup SF) φ + (2 * Real.pi)⁻¹ * B' * 2 * (s.sup SF) φ := by
          apply add_le_add
          ·
            have hSF00 : SchwartzMap.seminorm ℂ 0 0 ≤ s.sup SF := by
              calc SchwartzMap.seminorm ℂ 0 0
                  = SF (0, 0) := (SchwartzMap.schwartzSeminormFamily_apply ℂ _ ℂ 0 0).symm
                _ ≤ s.sup SF := Finset.le_sup (show (0, 0) ∈ s from by
                    simp only [s, Finset.mem_Iic]; constructor <;> omega)
            calc ‖∫ v in B, φ v • cauchyRiemannKernel v ∂μ‖
                ≤ ∫ v in B, ‖φ v • cauchyRiemannKernel v‖ ∂μ :=
                  norm_integral_le_integral_norm _
              _ = ∫ v in B, ‖φ v‖ * ‖cauchyRiemannKernel v‖ ∂μ := by
                  congr 1; ext v; exact norm_smul _ _
              _ ≤ ∫ v in B, (SchwartzMap.seminorm ℂ 0 0) φ * ‖cauchyRiemannKernel v‖ ∂μ := by
                  apply setIntegral_mono_on
                  · exact (hint.norm.congr (ae_of_all _ (fun v =>
                      norm_smul (φ v) (cauchyRiemannKernel v)))).integrableOn
                  · exact hE_intOn.norm.const_mul _
                  · exact hBmeas
                  · intro v _
                    gcongr
                    exact SchwartzMap.norm_le_seminorm ℂ φ v
              _ = (SchwartzMap.seminorm ℂ 0 0) φ * A := by
                  simp_rw [← smul_eq_mul]; exact integral_smul _ _
              _ ≤ (s.sup SF) φ * A := by
                  gcongr; exact hSF00 φ
              _ = A * (s.sup SF) φ := mul_comm _ _
          ·
            have hSF00 : SchwartzMap.seminorm ℂ 0 0 ≤ s.sup SF := by
              calc SchwartzMap.seminorm ℂ 0 0
                  = SF (0, 0) := (SchwartzMap.schwartzSeminormFamily_apply ℂ _ ℂ 0 0).symm
                _ ≤ s.sup SF := Finset.le_sup (show (0, 0) ∈ s from by
                    simp only [s, Finset.mem_Iic]; constructor <;> omega)
            have hSFp0 : SchwartzMap.seminorm ℂ p 0 ≤ s.sup SF := by
              calc SchwartzMap.seminorm ℂ p 0
                  = SF (p, 0) := (SchwartzMap.schwartzSeminormFamily_apply ℂ _ ℂ p 0).symm
                _ ≤ s.sup SF := Finset.le_sup (show (p, 0) ∈ s from by
                    simp only [s, Finset.mem_Iic]; constructor <;> omega)
            have hφ_int : Integrable (fun v => ‖(φ : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) v‖) μ := by
              exact φ.integrable.norm
            calc ‖∫ v in Bᶜ, φ v • cauchyRiemannKernel v ∂μ‖
                ≤ ∫ v in Bᶜ, ‖φ v • cauchyRiemannKernel v‖ ∂μ :=
                  norm_integral_le_integral_norm _
              _ = ∫ v in Bᶜ, ‖φ v‖ * ‖cauchyRiemannKernel v‖ ∂μ := by
                  congr 1; ext v; exact norm_smul _ _
              _ ≤ ∫ v in Bᶜ, ‖φ v‖ * (2 * Real.pi)⁻¹ ∂μ := by
                  apply setIntegral_mono_on
                  · exact (hint.norm.congr (ae_of_all _ (fun v =>
                      norm_smul (φ v) (cauchyRiemannKernel v)))).integrableOn
                  · exact (hφ_int.mul_const _).integrableOn
                  · exact hBmeas.compl
                  · intro v hv
                    have hv' : 1 ≤ ‖v‖ := by
                      simp only [Set.mem_compl_iff, B, Metric.mem_closedBall,
                        dist_zero_right, not_le] at hv
                      linarith
                    gcongr
                    exact cauchyRiemannKernel_norm_le v hv'
              _ = (2 * Real.pi)⁻¹ * ∫ v in Bᶜ, ‖φ v‖ ∂μ := by
                  simp_rw [mul_comm _ ((2 * Real.pi)⁻¹), ← smul_eq_mul]
                  exact integral_smul _ _
              _ ≤ (2 * Real.pi)⁻¹ * ∫ v, ‖φ v‖ ∂μ := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  exact setIntegral_le_integral hφ_int
                    (Eventually.of_forall fun v => norm_nonneg _)
              _ ≤ (2 * Real.pi)⁻¹ * (B' *
                    ((SchwartzMap.seminorm ℂ 0 0) φ +
                     (SchwartzMap.seminorm ℂ p 0) φ)) := by
                  gcongr
                  have h := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℂ μ φ 0 0
                  simp only [pow_zero, one_mul, zero_add] at h
                  convert h using 2
                  ext x; simp
              _ ≤ (2 * Real.pi)⁻¹ * (B' * (2 * (s.sup SF) φ)) := by
                  gcongr
                  have h1 : (SchwartzMap.seminorm ℂ 0 0) φ ≤ (s.sup SF) φ :=
                    hSF00 φ
                  have h2 : (SchwartzMap.seminorm ℂ p 0) φ ≤ (s.sup SF) φ :=
                    hSFp0 φ
                  linarith
              _ = (2 * Real.pi)⁻¹ * B' * 2 * (s.sup SF) φ := by ring
      _ = C * (s.sup SF) φ := by ring


set_option maxHeartbeats 1600000 in
set_option backward.privateInPublic true in
/-- The Cauchy-Riemann tempered distribution: the action `φ ↦ ∫ φ v • cauchyRiemannKernel v`,
packaged as a tempered distribution on `ℝ²`. -/
def cauchyRiemannDistribution : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (E := ℂ) (G := ℂ) (σ := RingHom.id ℂ)
      (fun φ => ∫ v : EuclideanSpace ℝ (Fin 2), φ v • cauchyRiemannKernel v)
      (fun f g => by
        simp only [SchwartzMap.add_apply, add_smul]
        exact integral_add (cauchyRiemannKernel_schwartz_integrable f)
          (cauchyRiemannKernel_schwartz_integrable g))
      (fun c f => by
        simp only [SchwartzMap.smul_apply, RingHom.id_apply]
        have : (fun v : EuclideanSpace ℝ (Fin 2) => (c • f v) • cauchyRiemannKernel v) =
            (fun v => c • (f v • cauchyRiemannKernel v)) := by
          ext v; simp [smul_eq_mul, mul_assoc]
        rw [this]
        exact integral_smul c _)
      cauchyRiemannKernel_integral_bound


set_option backward.privateInPublic true in
