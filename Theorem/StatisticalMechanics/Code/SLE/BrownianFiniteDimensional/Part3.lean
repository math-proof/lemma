/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Instance.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

theorem memLp_eval_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (t : I) :
    MemLp (fun x : EuclideanSpace ℝ I => x t) 2
      (brownianFiniteDimensionalLaw I) := by
  simpa only [EuclideanSpace.coe_proj] using
    (IsGaussian.memLp_dual (brownianFiniteDimensionalLaw I)
      (EuclideanSpace.proj t) 2 (by simp))


theorem brownianFiniteDimensionalLaw_measurePreserving_eval
    (I : Finset ℝ) (t : I) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => x t)
      (brownianFiniteDimensionalLaw I)
      (ProbabilityTheory.gaussianReal 0 |(t : ℝ)|.toNNReal) := by
  simpa [brownianFiniteDimensionalLaw, brownianCovarianceMatrix] using
    (ProbabilityTheory.measurePreserving_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I) (μ := (0 : EuclideanSpace ℝ I))
      (i := t))

theorem integral_increment_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    ∫ x, (x t - x s) ∂(brownianFiniteDimensionalLaw I) = 0 := by
  let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
  change ∫ x, L x ∂(brownianFiniteDimensionalLaw I) = 0
  rw [L.integral_comp_id_comm IsGaussian.integrable_id]
  simp [brownianFiniteDimensionalLaw]

theorem variance_increment_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t : I) :
    Var[(fun x : EuclideanSpace ℝ I => x t - x s);
      brownianFiniteDimensionalLaw I] = |(t : ℝ) - (s : ℝ)| := by
  have ht : MemLp (fun x : EuclideanSpace ℝ I => x t) 2
      (brownianFiniteDimensionalLaw I) :=
    memLp_eval_brownianFiniteDimensionalLaw I t
  have hs : MemLp (fun x : EuclideanSpace ℝ I => x s) 2
      (brownianFiniteDimensionalLaw I) :=
    memLp_eval_brownianFiniteDimensionalLaw I s
  rw [variance_fun_sub ht hs]
  simp_rw [brownianFiniteDimensionalLaw,
    ProbabilityTheory.variance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    ProbabilityTheory.covariance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    brownianCovarianceMatrix, brownianCovariance_self, brownianCovariance_eq]
  rw [abs_sub_comm]
  ring


theorem brownianFiniteDimensionalLaw_measurePreserving_increment
    (I : Finset ℝ) (s t : I) :
    MeasurePreserving (fun x : EuclideanSpace ℝ I => x t - x s)
      (brownianFiniteDimensionalLaw I)
      (ProbabilityTheory.gaussianReal 0 |(t : ℝ) - (s : ℝ)|.toNNReal) where
  measurable := by fun_prop
  map_eq := by
    let L : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
    change (brownianFiniteDimensionalLaw I).map L = _
    rw [IsGaussian.map_eq_gaussianReal]
    congr 2
    · exact integral_increment_brownianFiniteDimensionalLaw I s t
    · exact variance_increment_brownianFiniteDimensionalLaw I s t

theorem covariance_disjoint_increments_brownianFiniteDimensionalLaw
    (I : Finset ℝ) (s t u v : I)
    (hst : (s : ℝ) ≤ t) (htu : (t : ℝ) ≤ u) (huv : (u : ℝ) ≤ v) :
    cov[(fun x : EuclideanSpace ℝ I => x t - x s),
      (fun x : EuclideanSpace ℝ I => x v - x u);
      brownianFiniteDimensionalLaw I] = 0 := by
  have hs := memLp_eval_brownianFiniteDimensionalLaw I s
  have ht := memLp_eval_brownianFiniteDimensionalLaw I t
  have hu := memLp_eval_brownianFiniteDimensionalLaw I u
  have hv := memLp_eval_brownianFiniteDimensionalLaw I v
  have hvu : MemLp (fun x : EuclideanSpace ℝ I => x v - x u) 2
      (brownianFiniteDimensionalLaw I) := by
    convert hv.sub hu using 1
  rw [covariance_fun_sub_left ht hs hvu,
    covariance_fun_sub_right ht hv hu,
    covariance_fun_sub_right hs hv hu]
  simp_rw [brownianFiniteDimensionalLaw,
    ProbabilityTheory.covariance_eval_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I),
    brownianCovarianceMatrix, brownianCovariance_eq]
  have hsv : (s : ℝ) ≤ v := hst.trans (htu.trans huv)
  have hsu : (s : ℝ) ≤ u := hst.trans htu
  have htv : (t : ℝ) ≤ v := htu.trans huv
  simp [abs_of_nonneg (sub_nonneg.mpr htv),
    abs_of_nonneg (sub_nonneg.mpr htu),
    abs_of_nonneg (sub_nonneg.mpr hsv),
    abs_of_nonneg (sub_nonneg.mpr hsu)]
  ring


theorem brownianFiniteDimensionalLaw_indepFun_increments
    (I : Finset ℝ) (s t u v : I)
    (hst : (s : ℝ) ≤ t) (htu : (t : ℝ) ≤ u) (huv : (u : ℝ) ≤ v) :
    IndepFun (fun x : EuclideanSpace ℝ I => x t - x s)
      (fun x : EuclideanSpace ℝ I => x v - x u)
      (brownianFiniteDimensionalLaw I) := by
  let L₁ : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj t - EuclideanSpace.proj s
  let L₂ : EuclideanSpace ℝ I →L[ℝ] ℝ := EuclideanSpace.proj v - EuclideanSpace.proj u
  have hpair : HasGaussianLaw (fun x : EuclideanSpace ℝ I =>
      (x t - x s, x v - x u)) (brownianFiniteDimensionalLaw I) := by
    have hL : HasGaussianLaw (⇑(L₁.prod L₂)) (brownianFiniteDimensionalLaw I) :=
      IsGaussian.hasGaussianLaw (L₁.prod L₂).continuous.aemeasurable
    have hfun : (fun x : EuclideanSpace ℝ I => (x t - x s, x v - x u)) = ⇑(L₁.prod L₂) := by
      ext x
      · simp [L₁, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
          EuclideanSpace.coe_proj]
      · simp [L₂, ContinuousLinearMap.prod_apply, ContinuousLinearMap.sub_apply,
          EuclideanSpace.coe_proj]
    simpa [hfun] using hL
  exact hpair.indepFun_of_covariance_eq_zero
    (covariance_disjoint_increments_brownianFiniteDimensionalLaw I s t u v hst htu huv)


theorem brownianFiniteDimensionalLaw_restrict
    {I J : Finset ℝ} (hJI : J ⊆ I) :
    MeasurePreserving (EuclideanSpace.restrict₂ hJI)
      (brownianFiniteDimensionalLaw I) (brownianFiniteDimensionalLaw J) := by
  have hsub : (brownianCovarianceMatrix I).submatrix
      (fun i : J => ⟨i.1, hJI i.2⟩) (fun i : J => ⟨i.1, hJI i.2⟩) =
      brownianCovarianceMatrix J := by
    ext s t
    simp [brownianCovarianceMatrix, Matrix.submatrix_apply]
  have h0 : EuclideanSpace.restrict₂ hJI (0 : EuclideanSpace ℝ I) = 0 := by
    simp
  simpa [brownianFiniteDimensionalLaw, hsub, h0] using
    ProbabilityTheory.measurePreserving_restrict₂_multivariateGaussian
      (brownianCovarianceMatrix_posSemidef I) hJI
      (μ := (0 : EuclideanSpace ℝ I))


end StatMech.SLE
