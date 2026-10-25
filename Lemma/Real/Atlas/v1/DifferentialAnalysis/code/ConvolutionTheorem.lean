import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
open TemperedDistribution SchwartzMap DifferentialOperators Distribution
open scoped SchwartzMap LineDeriv Pointwise
open TemperedDistribution SchwartzMap DifferentialOperators Distribution SobolevSpace SchwartzRepresentation


namespace DifferentialOperators

/--
[tempDistSchwartzConv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma tempDistSchwartzConv_apply
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)}
  {x : E} :
-- imply
  tempDistSchwartzConv u φ x = u (compSubConstCLM ℂ x φ) :=
-- proof
  rfl

end DifferentialOperators

namespace DifferentialOperators

/--
[tempDistSchwartzConv_contDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma tempDistSchwartzConv_contDiff
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)} :
-- imply
  ContDiff ℝ (⊤ : ℕ∞) (tempDistSchwartzConv u φ) :=
-- proof
  contDiff_schwartz_translation_clm u φ

end DifferentialOperators

namespace DifferentialOperators

/--
[tempDistSchwartzConv_polynomial_growth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma tempDistSchwartzConv_polynomial_growth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)} :
-- imply
  ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x : E, ‖tempDistSchwartzConv u φ x‖ ≤ C * (1 + ‖x‖) ^ k := by
-- proof
  let q : Seminorm ℂ 𝓢(E, ℂ) := (normSeminorm ℂ ℂ).comp u.toLinearMap
  have hq_cont : Continuous q := continuous_norm.comp u.cont
  obtain ⟨s, C_u, _, hCu_le⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ E ℂ) q hq_cont
  let k : ℕ := s.sup (fun m => m.1)
  let C_φ : NNReal := s.sup (fun m =>
    ⟨(Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ,
      apply_nonneg _ _⟩)
  refine ⟨k, ↑C_u * 2 ^ k * ↑C_φ, by positivity, fun x => ?_⟩
  have h1 : q (compSubConstCLM ℂ x φ) ≤
    (C_u • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) :=
    hCu_le (compSubConstCLM ℂ x φ)
  have h2 : (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) ≤
    (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro m hm
    have hbound := TemperedDistributions.SchwartzMap.seminorm_compSubConst_le ℂ m.1 m.2 φ x
    have hm1_le : m.1 ≤ k := Finset.le_sup (f := fun m => m.1) hm
    have h1x : 1 ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hCφ_le : (Finset.Iic (m.1, m.2)).sup
      (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ ≤ ↑C_φ := by
      exact_mod_cast Finset.le_sup (f := fun m : ℕ × ℕ =>
        (⟨(Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ,
          apply_nonneg _ _⟩ : NNReal)) hm
    calc SchwartzMap.seminorm ℂ m.1 m.2 (compSubConstCLM ℂ x φ)
      ≤ (1 + ‖x‖) ^ m.1 * 2 ^ m.1 *
        (Finset.Iic (m.1, m.2)).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ :=
        hbound
      _ ≤ (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
        have hp1 := pow_le_pow_right₀ h1x hm1_le
        have hp2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm1_le
        calc (1 + ‖x‖) ^ m.1 * 2 ^ m.1 *
          ((Finset.Iic (m.1, m.2)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ
          ≤ (1 + ‖x‖) ^ k * 2 ^ k *
            ((Finset.Iic (m.1, m.2)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ := by
              apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
              exact mul_le_mul hp1 hp2 (by positivity) (by positivity)
          _ ≤ (1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ := by
            exact mul_le_mul_of_nonneg_left hCφ_le (by positivity)
  have h3 : q (compSubConstCLM ℂ x φ) = ‖u (compSubConstCLM ℂ x φ)‖ := rfl
  calc ‖u (compSubConstCLM ℂ x φ)‖
    = q (compSubConstCLM ℂ x φ) := h3.symm
    _ ≤ (C_u • s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) := h1
    _ = ↑C_u * (s.sup (schwartzSeminormFamily ℂ E ℂ)) (compSubConstCLM ℂ x φ) := rfl
    _ ≤ ↑C_u * ((1 + ‖x‖) ^ k * 2 ^ k * ↑C_φ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ↑C_u * 2 ^ k * ↑C_φ * (1 + ‖x‖) ^ k := by ring

end DifferentialOperators

namespace DifferentialOperators

/--
[tempDistSchwartzConv_deriv_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma tempDistSchwartzConv_deriv_right
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)}
-- given
  (x h : E) :
-- imply
  fderiv ℝ (tempDistSchwartzConv u φ) x h = - tempDistSchwartzConv u (postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.apply ℝ ℂ h) (fderivCLM ℝ E ℂ φ)) x := by
-- proof
  have hevalCLM_eq : SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ φ) =
    postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.apply ℝ ℂ h) (fderivCLM ℝ E ℂ φ) := by
    ext y
    simp [SchwartzMap.evalCLM_apply_apply, SchwartzMap.postcompCLM_apply,
      SchwartzMap.fderivCLM_apply]
  set ψ' := SchwartzMap.fderivCLM ℂ E ℂ φ
  set g : E →L[ℝ] ℂ :=
    -({ toFun := fun v => u (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ'))
      map_add' := by
        intro h₁ h₂
        have : SchwartzMap.evalCLM ℂ E ℂ (h₁ + h₂) ψ' =
          SchwartzMap.evalCLM ℂ E ℂ h₁ ψ' + SchwartzMap.evalCLM ℂ E ℂ h₂ ψ' := by
          ext y; simp only [SchwartzMap.evalCLM_apply_apply, map_add, SchwartzMap.add_apply]
        rw [this, map_add, map_add]
      map_smul' := by
        intro r v
        simp only [RingHom.id_apply]
        have : SchwartzMap.evalCLM ℂ E ℂ (r • v) ψ' =
          (r : ℂ) • SchwartzMap.evalCLM ℂ E ℂ v ψ' := by
          ext y
          simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.smul_apply, map_smul]; rfl
        rw [this, map_smul, map_smul]; rfl } : E →ₗ[ℝ] ℂ).toContinuousLinearMap
  have hHasFDeriv : HasFDerivAt (fun x => u (compSubConstCLM ℂ x φ)) g x := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hrw : ∀ v : E,
      u (compSubConstCLM ℂ (x + v) φ) - u (compSubConstCLM ℂ x φ) - g v =
      u (compSubConstCLM ℂ x
        (compSubConstCLM ℂ v φ - φ + SchwartzMap.evalCLM ℂ E ℂ v ψ')) := by
      intro v
      have hcomp : compSubConstCLM ℂ (x + v) φ =
        compSubConstCLM ℂ x (compSubConstCLM ℂ v φ) := by
        rw [SchwartzMap.compSubConstCLM_comp]; congr 1; abel
      have hg : g v = -u (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ')) := rfl
      rw [hcomp, hg, sub_neg_eq_add, ← map_sub u, ← map_add u,
        ← map_sub (compSubConstCLM ℂ x), ← map_add (compSubConstCLM ℂ x)]
    simp_rw [hrw]
    exact schwartz_taylor_remainder_isLittleO u φ x
  have hfderiv_eq : fderiv ℝ (fun x => u (compSubConstCLM ℂ x φ)) x = g :=
    hHasFDeriv.fderiv
  have heq : tempDistSchwartzConv u φ = fun x => u (compSubConstCLM ℂ x φ) := rfl
  rw [show fderiv ℝ (tempDistSchwartzConv u φ) x h =
    fderiv ℝ (fun x => u (compSubConstCLM ℂ x φ)) x h from by rw [heq]]
  rw [hfderiv_eq]
  show g h = _
  simp only [tempDistSchwartzConv_apply]
  show -u (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ h ψ')) = _
  congr 1

end DifferentialOperators

namespace DifferentialOperators

/--
[tempDistSchwartzConv_vanishes_away_from_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma tempDistSchwartzConv_vanishes_away_from_support
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {u : 𝓢'(E, ℂ)}
  {φ : 𝓢(E, ℂ)}
  {x : E}
-- given
  (hdisjoint : Disjoint (tsupport (fun y => (φ : E → ℂ) (y - x))) (closure (Distribution.dsupport u))) :
-- imply
  tempDistSchwartzConv u φ x = 0 := by
-- proof
  have hcl : closure (Distribution.dsupport u) = Distribution.dsupport u :=
    Distribution.isClosed_dsupport.closure_eq
  rw [hcl] at hdisjoint
  unfold tempDistSchwartzConv
  set ψ := compSubConstCLM ℂ x φ with hψ_def
  have hψ_eq : (⇑ψ : E → ℂ) = fun y => φ (y - x) := by
    ext z; rfl
  have hψ_disj : Disjoint (tsupport (⇑ψ)) (Distribution.dsupport u) := by
    rwa [hψ_eq]
  have h_van : ∀ (χ : 𝓢(E, ℂ)), HasCompactSupport χ → tsupport (⇑χ) ⊆ tsupport (⇑ψ) → u χ = 0 := by
    intro χ hχ hts
    exact tempered_vanishing_outside_dsupport u χ hχ (hψ_disj.mono_left hts)
  have htend : Filter.Tendsto (fun n => SchwartzMap.bumpCutoffMul n ψ) Filter.atTop (nhds ψ) := by
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ ψ]
    intro ⟨k, j⟩ ε hε
    have h := SchwartzMap.seminorm_cutoff_sub_tendsto ℂ ψ k j
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [Filter.Ici_mem_atTop N] with m hm
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    have h1 := hN m hm
    rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h1
    calc (SchwartzMap.seminorm ℂ k j) (SchwartzMap.bumpCutoffMul m ψ - ψ)
      = (SchwartzMap.seminorm ℂ k j) (ψ - SchwartzMap.bumpCutoffMul m ψ) := by
        rw [← map_neg_eq_map]; congr 1; abel
      _ < ε := h1
  have h_u_cont := u.cont
  have h_u_tend : Filter.Tendsto (fun n => u (SchwartzMap.bumpCutoffMul n ψ)) Filter.atTop (nhds (u ψ)) :=
    h_u_cont.continuousAt.tendsto.comp htend
  have h_all_zero : ∀ n, u (SchwartzMap.bumpCutoffMul n ψ) = 0 := by
    intro n
    apply h_van
    · exact SchwartzMap.bumpCutoffMul_hasCompactSupport n ψ
    ·
      apply closure_mono
      intro y hy
      rw [Function.mem_support] at hy ⊢
      simp only [SchwartzMap.bumpCutoffMul_apply] at hy
      intro habs
      exact hy (by rw [habs, smul_zero])
  have h_const_zero : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds (u ψ)) := by
    convert h_u_tend using 1
    ext n
    exact (h_all_zero n).symm
  exact tendsto_nhds_unique h_const_zero tendsto_const_nhds

end DifferentialOperators

namespace DifferentialOperators

/--
[theorem_11_6_full](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma theorem_11_6_full
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  (∀ (m x : EuclideanSpace ℝ (Fin n)), temperedConvolution (TemperedDistributions.distribDerivCLM m u) φ x = lineDeriv ℝ (temperedConvolution u φ) x m ∧ lineDeriv ℝ (temperedConvolution u φ) x m = temperedConvolution u (∂_{m} φ) x) ∧ (HasCompactSupport φ → Function.support (temperedConvolution u φ) ⊆ dsupport u + tsupport (↑φ : EuclideanSpace ℝ (Fin n) → ℂ)) :=
-- proof
  ⟨fun m x => ⟨hormander_convolution_deriv_left u φ m x,
    hormander_convolution_deriv_right u φ m x⟩,
    fun hφ => hormander_convolution_support u φ hφ⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[temperedConvolution_iterPartialDeriv_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionTheorem.lean)
-/
@[path]
lemma temperedConvolution_iterPartialDeriv_coord
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
  {j : Fin n}
  {k : ℕ}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  temperedConvolution (iteratedPartialDerivDistrib n j k u) φ x = temperedConvolution u (iterSchwartzDerivCoord j k φ) x := by
-- proof
  induction k generalizing u φ with
  | zero =>
    simp only [iteratedPartialDerivDistrib, iterSchwartzDerivCoord, Function.iterate_zero,
      id_eq]
  | succ k ih =>
    have h_distrib : iteratedPartialDerivDistrib n j (k + 1) u =
      TemperedDistributions.distribDerivCLM
        (EuclideanSpace.single j (1 : ℝ))
        (iteratedPartialDerivDistrib n j k u) := by
      simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp_apply]
    have h_schwartz : iterSchwartzDerivCoord j (k + 1) φ =
      iterSchwartzDerivCoord j k (∂_{EuclideanSpace.single j (1 : ℝ)} φ) := by
      simp only [iterSchwartzDerivCoord, Function.iterate_succ, Function.comp_apply]
    have hstep : temperedConvolution
      (TemperedDistributions.distribDerivCLM (EuclideanSpace.single j (1 : ℝ))
        (iteratedPartialDerivDistrib n j k u)) φ x =
      temperedConvolution (iteratedPartialDerivDistrib n j k u)
        (∂_{EuclideanSpace.single j (1 : ℝ)} φ) x := by
      have hleft := hormander_convolution_deriv_left
        (iteratedPartialDerivDistrib n j k u) φ
        (EuclideanSpace.single j (1 : ℝ)) x
      have hright := hormander_convolution_deriv_right
        (iteratedPartialDerivDistrib n j k u) φ
        (EuclideanSpace.single j (1 : ℝ)) x
      exact hleft.trans hright
    rw [h_distrib, hstep, ih, h_schwartz]
end DifferentialOperators



-- created on 2026-10-23
