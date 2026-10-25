import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontCharacterization
open MeasureTheory Set ConeSupport
open scoped SchwartzMap


namespace ConeSupport

/--
[clm_norm_le_sum_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontCharacterization.lean)
-/
@[path]
lemma clm_norm_le_sum_basis
  {n : ℕ}
  {L : E n →L[ℝ] ℂ} :
-- imply
  ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ := by
-- proof
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hv_decomp : v = ∑ i : Fin n, (v i : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv_decomp]
  calc ‖L (∑ i, (v i : ℝ) • EuclideanSpace.single i 1)‖
    = ‖∑ i, (v i : ℝ) • L (EuclideanSpace.single i 1)‖ := by
      simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖(v i : ℝ) • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖L (EuclideanSpace.single i 1)‖ := by simp
    _ ≤ ∑ i, ‖v‖ * ‖L (EuclideanSpace.single i 1)‖ := by
      gcongr with i _; exact PiLp.norm_apply_le v i
    _ = (∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖) * ‖v‖ := by
      simp_rw [mul_comm ‖v‖ _]; rw [← Finset.sum_mul]

end ConeSupport

namespace ConeSupport

/--
[norm_iteratedFDeriv_fderiv_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontCharacterization.lean)
-/
@[path]
lemma norm_iteratedFDeriv_fderiv_le_sum
  {n : ℕ}
  {m : ℕ}
  {f : E n → ℂ}
  {x : E n}
-- given
  (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
-- imply
  ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ := by
-- proof
  have hfderiv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by simp)
  have hcomp : ∀ i : Fin n,
    (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) =
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ f) := by
    intro i; ext y; simp [ContinuousLinearMap.apply_apply]
  have hcomp2 : ∀ i : Fin n,
    iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x =
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).compContinuousMultilinearMap
      (iteratedFDeriv ℝ m (fderiv ℝ f) x) := by
    intro i
    rw [hcomp i]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left _
      hfderiv_smooth.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  set M := iteratedFDeriv ℝ m (fderiv ℝ f) x
  apply (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr
  intro v
  calc ‖M v‖
    ≤ ∑ i : Fin n, ‖M v (EuclideanSpace.single i 1)‖ :=
      clm_norm_le_sum_basis (M v)
    _ = ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x v‖ := by
      congr 1; ext i; rw [hcomp2]; rfl
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ * ∏ j, ‖v j‖ := by
      gcongr with i _
      exact (iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x).le_opNorm v
    _ = (∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖) * ∏ j, ‖v j‖ := by
      rw [Finset.sum_mul]
set_option maxHeartbeats 800000 in

end ConeSupport

namespace ConeSupport

/--
[temperedConvolution_iteratedFDeriv_polynomial_growth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontCharacterization.lean)
-/
@[path]
lemma temperedConvolution_iteratedFDeriv_polynomial_growth
  {n : ℕ}
  {u : TemperedDistribution (E n) ℂ}
  {φ : 𝓢(E n, ℂ)}
  {m : ℕ} :
-- imply
  ∃ (k : ℕ) (C : ℝ), ∀ x : E n, ‖iteratedFDeriv ℝ m (DifferentialOperators.temperedConvolution u φ) x‖ ≤ C * (1 + ‖x‖) ^ k := by
-- proof
  revert φ
  induction m with
  | zero =>
    intro φ
    obtain ⟨C, k, hC_pos, hbound⟩ :=
      DifferentialOperators.hormander_convolution_polynomial_growth u φ
    refine ⟨2 * k, C, fun x => ?_⟩
    simp only [iteratedFDeriv_zero_eq_comp]
    have h1 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    have h1' : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 : ℝ) + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
    have h3 : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    have rpow_bound : (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖x‖) ^ (2 * k) := by
      calc (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)
        ≤ ((1 + ‖x‖) ^ 2) ^ ((k : ℝ) / 2) :=
          Real.rpow_le_rpow h3.le h2 (by positivity)
        _ = (1 + ‖x‖) ^ ((↑(2 : ℕ) : ℝ) * ((k : ℝ) / 2)) := by
          rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul h1]
        _ = (1 + ‖x‖) ^ (↑k : ℝ) := by congr 1; push_cast; ring
        _ = (1 + ‖x‖) ^ (k : ℕ) := Real.rpow_natCast _ _
        _ ≤ (1 + ‖x‖) ^ (2 * k) := pow_le_pow_right₀ h1' (by omega)
    calc ‖(continuousMultilinearCurryFin0 ℝ (E n) ℂ).symm
      (DifferentialOperators.temperedConvolution u φ x)‖
      = ‖DifferentialOperators.temperedConvolution u φ x‖ :=
        LinearIsometryEquiv.norm_map _ _
      _ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := hbound x
      _ ≤ C * (1 + ‖x‖) ^ (2 * k) := by linarith [mul_le_mul_of_nonneg_left rpow_bound hC_pos.le]
  | succ m ih =>
    intro φ
    have hsmooth := DifferentialOperators.hormander_convolution_smooth u φ
    have hderiv : ∀ i : Fin n, ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x : E n,
      ‖iteratedFDeriv ℝ m (fun y =>
        fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
          (EuclideanSpace.single i 1)) x‖ ≤ C * (1 + ‖x‖) ^ k := by
      intro i
      set ei : E n := EuclideanSpace.single i 1
      have hcomp : (fun y => fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y ei) =
        DifferentialOperators.temperedConvolution u (LineDeriv.lineDerivOp ei φ) := by
        ext y
        rw [← (hsmooth.differentiable (by simp [WithTop.coe_ne_zero]) y).lineDeriv_eq_fderiv]
        exact DifferentialOperators.hormander_convolution_deriv_right u φ ei y
      rw [hcomp]
      obtain ⟨k, C, hC⟩ := ih (LineDeriv.lineDerivOp ei φ)
      exact ⟨k, max C 0, le_max_right _ _, fun x =>
        (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
    choose ks Cs hCs_nn hCs_bound using hderiv
    set K := Finset.univ.sup ks
    have hunif : ∀ (i : Fin n) (x : E n),
      ‖iteratedFDeriv ℝ m (fun y =>
        fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
          (EuclideanSpace.single i 1)) x‖ ≤ Cs i * (1 + ‖x‖) ^ K := by
      intro i x
      calc _ ≤ Cs i * (1 + ‖x‖) ^ ks i := hCs_bound i x
        _ ≤ Cs i * (1 + ‖x‖) ^ K := by
          apply mul_le_mul_of_nonneg_left _ (hCs_nn i)
          exact pow_le_pow_right₀ (by linarith [norm_nonneg x])
            (Finset.le_sup (f := ks) (Finset.mem_univ i))
    refine ⟨K, (∑ i : Fin n, Cs i) + 1, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
    calc ‖iteratedFDeriv ℝ m (fderiv ℝ (DifferentialOperators.temperedConvolution u φ)) x‖
      ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y =>
        fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
          (EuclideanSpace.single i 1)) x‖ :=
        norm_iteratedFDeriv_fderiv_le_sum _ hsmooth x
      _ ≤ ∑ i : Fin n, Cs i * (1 + ‖x‖) ^ K :=
        Finset.sum_le_sum (fun i _ => hunif i x)
      _ = (∑ i : Fin n, Cs i) * (1 + ‖x‖) ^ K := by rw [Finset.sum_mul]
      _ ≤ ((∑ i : Fin n, Cs i) + 1) * (1 + ‖x‖) ^ K := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
/-- Pairing identity: testing the Schwartz convolution `u ∗ φ` against a Schwartz function `θ`
equals the integral of `θ` against the pointwise tempered convolution. -/
end ConeSupport



-- created on 2026-10-23
