import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.DiffOpSobolev.Part3
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory DiffOpSobolev
open scoped SchwartzMap ContDiff FourierTransform
open TestFunctions
open TemperedDistributions (distribDerivCLM)


namespace DiffOpSobolev

/--
[schwartz_pairing_nondeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma schwartz_pairing_nondeg
  {n : ℕ}
  {ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (h : ∀ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ) f ψ = 0) :
-- imply
  ψ = 0 := by
-- proof
  set E := EuclideanSpace ℝ (Fin n)
  have hψ_ae : (ψ : E → ℂ) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (ψ.integrable.locallyIntegrable)
    intro g hg_smooth hg_supp
    let f_s : 𝓢(E, ℂ) := (hg_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg_smooth)
    specialize h f_s
    simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply] at h
    convert h using 1
    congr 1; ext x
    simp only [f_s, Function.comp, HasCompactSupport.toSchwartzMap_toFun]
    change (g x : ℂ) * ψ x = ψ x * (g x : ℂ)
    ring
  exact SchwartzMap.ext (fun x => congr_fun
    ((Continuous.ae_eq_iff_eq volume ψ.continuous continuous_const).mp hψ_ae) x)

end DiffOpSobolev

namespace DiffOpSobolev

/--
[hall_implies_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma hall_implies_eq
  {n : ℕ}
  {ι : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {f₀ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
  {S' : Finset (𝓢(EuclideanSpace ℝ (Fin n), ℂ))}
  {ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hι : ι = SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ)
  (hf₀ : ∀ φ ∈ S', ι f₀ φ = u φ)
  (hall : ∀ g, (∀ φ ∈ S', ι g φ = 0) → ι g ψ = 0) :
-- imply
  ι f₀ ψ = u ψ := by
-- proof
  induction S' using Finset.cons_induction generalizing ψ with
  | empty =>
    have hψ0 : ψ = 0 := by
      subst hι
      exact schwartz_pairing_nondeg n ψ (fun f => hall f (fun φ h => absurd h (by simp)))
    simp [hψ0]
  | cons φ₀ S'' hφ₀S'' ih =>
    by_cases h_inner : ∀ g, (∀ φ ∈ S'', ι g φ = 0) → ι g ψ = 0
    · exact ih (fun φ hφ => hf₀ φ (Finset.mem_cons.mpr (Or.inr hφ))) ψ h_inner
    · push Not at h_inner
      obtain ⟨g₀, hg₀_zero, hg₀_ne⟩ := h_inner
      have hg₀φ₀ : ι g₀ φ₀ ≠ 0 := by
        intro heq0
        exact hg₀_ne (hall g₀ (fun φ hφ => by
          rw [Finset.mem_cons] at hφ
          obtain rfl | hφ := hφ
          · exact heq0
          · exact hg₀_zero φ hφ))
      set c₀ := ι g₀ ψ / ι g₀ φ₀
      suffices key : ι f₀ (ψ - c₀ • φ₀) = u (ψ - c₀ • φ₀) by
        have h1 : ι f₀ ψ - c₀ * ι f₀ φ₀ = u ψ - c₀ * u φ₀ := by
          simp only [map_sub, map_smul, smul_eq_mul] at key
          exact key
        have h2 : ι f₀ φ₀ = u φ₀ := hf₀ φ₀ (Finset.mem_cons.mpr (Or.inl rfl))
        linear_combination h1 + c₀ * h2
      apply ih (fun φ hφ => hf₀ φ (Finset.mem_cons.mpr (Or.inr hφ)))
      intro g hg
      simp only [map_sub, map_smul, smul_eq_mul]
      set a := ι g φ₀ / ι g₀ φ₀
      have hg' : ∀ φ ∈ Finset.cons φ₀ S'' hφ₀S'', ι (g - a • g₀) φ = 0 := by
        intro φ hφ
        simp only [map_sub, map_smul]
        rw [Finset.mem_cons] at hφ
        obtain rfl | hφ := hφ
        · simp [a, div_mul_cancel₀ _ hg₀φ₀]
        · simp [hg φ hφ, hg₀_zero φ hφ]
      have hval' : ι g ψ - a * ι g₀ ψ = 0 := by
        have hval := hall (g - a • g₀) hg'
        simp only [map_sub, map_smul] at hval
        exact hval
      have h2 : a * ι g₀ ψ = c₀ * ι g φ₀ := by
        simp only [a, c₀]
        field_simp
      linear_combination hval' + h2

end DiffOpSobolev

namespace DiffOpSobolev

/--
[schwartz_joint_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma schwartz_joint_eval
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {S : Finset (𝓢(EuclideanSpace ℝ (Fin n), ℂ))} :
-- imply
  ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ φ ∈ S, (SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ) f φ = u φ := by
-- proof
  set ι := SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ
  induction S using Finset.cons_induction with
  | empty => exact ⟨0, fun φ h => absurd h (by simp)⟩
  | cons ψ S' hψS' ih =>
    obtain ⟨f₀, hf₀⟩ := ih
    by_cases heq : ι f₀ ψ = u ψ
    · exact ⟨f₀, fun φ hφ => by
      rw [Finset.mem_cons] at hφ
      obtain rfl | hφ := hφ
      · exact heq
      · exact hf₀ φ hφ⟩
    · have hg_exists : ∃ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∀ φ ∈ S', ι g φ = 0) ∧ ι g ψ ≠ 0 := by
      by_contra hall
      push Not at hall
      exact heq (hall_implies_eq n ι rfl u f₀ S' hf₀ ψ hall)
      obtain ⟨g, hg_zero, hg_ne⟩ := hg_exists
      let c := (u ψ - ι f₀ ψ) / ι g ψ
      have ι_add_smul (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
        (ι (f₀ + c • g)) φ = ι f₀ φ + c * ι g φ := by
        simp [map_add, map_smul, smul_eq_mul]
      refine ⟨f₀ + c • g, fun φ hφ => ?_⟩
      rw [Finset.mem_cons] at hφ
      obtain rfl | hφ := hφ
      · rw [ι_add_smul]
        simp [c, div_mul_cancel₀ _ hg_ne, add_sub_cancel]
      · rw [ι_add_smul, hg_zero φ hφ, mul_zero, add_zero, hf₀ φ hφ]

end DiffOpSobolev

namespace DiffOpSobolev

/--
[schwartz_weakly_dense](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma schwartz_weakly_dense
  {n : ℕ} :
-- imply
  DenseRange (SchwartzMap.toTemperedDistributionCLM (EuclideanSpace ℝ (Fin n)) ℂ) := by
-- proof
  set E := EuclideanSpace ℝ (Fin n) with hE
  set ι := SchwartzMap.toTemperedDistributionCLM E ℂ with hι
  intro u
  rw [mem_closure_iff_nhds]
  intro V hV
  choose f_S hf_S using fun S : Finset (𝓢(E, ℂ)) => schwartz_joint_eval n u S
  have htendsto : Tendsto (fun S => ι (f_S S)) atTop (𝓝 u) := by
    rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto]
    intro φ
    apply tendsto_const_nhds.congr'
    rw [EventuallyEq, Filter.eventually_atTop]
    exact ⟨{φ}, fun S hS => (hf_S S φ (hS (Finset.mem_singleton.mpr rfl))).symm⟩
  have hev : ∀ᶠ S in atTop, ι (f_S S) ∈ V := htendsto hV
  obtain ⟨S₀, hS₀⟩ := hev.exists
  exact ⟨ι (f_S S₀), hS₀, ⟨f_S S₀, rfl⟩⟩

end DiffOpSobolev

namespace DiffOpSobolev

/--
[tailMultiIndexSum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma tailMultiIndexSum_zero
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ} :
-- imply
  tailMultiIndexSum α 0 = ∑ i, α i := by
-- proof
  simp [tailMultiIndexSum]

end DiffOpSobolev

namespace DiffOpSobolev

/--
[multiIndexDeriv_memHs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma multiIndexDeriv_memHs
  {n : ℕ}
  {m : ℝ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : MemHs n m u) :
-- imply
  MemHs n (m - ↑(∑ i, α i)) (iteratedDistribDeriv n α u) :=
-- proof
  memHs_iteratedDistribDeriv α u hu
/-- Iteratively multiplying by Fourier variables equals smul-left multiplication by
the symbol of the monomial `x^α`, when acting on a distribution. -/
section WitnessAeBound
open TestFunctions
open TemperedDistributions (distribDerivCLM)

end DiffOpSobolev

namespace DiffOpSobolev

/--
[sobolev_witness_ae_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma sobolev_witness_ae_unique
  {n : ℕ}
  {s : ℝ}
  {g₁ g₂ : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg₁ : MemLp g₁ 2)
  (hg₂ : MemLp g₂ 2)
  (hint : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₁ ξ * φ ξ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ) :
-- imply
  g₁ =ᵐ[volume] g₂ := by
-- proof
  have hg₁_li : LocallyIntegrable g₁ volume :=
    hg₁.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg₂_li : LocallyIntegrable g₂ volume :=
    hg₂.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_of_integral_contDiff_smul_eq hg₁_li hg₂_li
  intro g_test hg_smooth hg_supp
  have hw_htg : (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
      (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1; ring
  have hψ_smooth := hg_smooth.mul hw_htg.1
  have hψ_supp : HasCompactSupport (fun ξ => g_test ξ * sobolevWeight n s ξ) :=
    hg_supp.mul_right
  set φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hψ_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ_smooth)
  have key := hint φ
  have heq_lhs : (fun x => g_test x • g₁ x) =
    (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  have heq_rhs : (fun x => g_test x • g₂ x) =
    (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  calc ∫ x, g_test x • g₁ x
    = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x := congr_arg _ heq_lhs
    _ = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x := key
    _ = ∫ x, g_test x • g₂ x := congr_arg _ heq_rhs.symm
set_option maxHeartbeats 800000 in

end DiffOpSobolev

namespace DiffOpSobolev

/--
[memHs_distribDeriv_with_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma memHs_distribDeriv_with_bound
  {n : ℕ}
  {s : ℝ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg_mem : MemLp g 2)
  (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
-- imply
  ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g_new 2 ∧ (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (distribDerivCLM (F := ℂ) (EuclideanSpace.single j (1 : ℝ)) u)) φ = ∫ ξ, (sobolevWeight n (s - 1) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧ (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖) := by
-- proof
  set ej := EuclideanSpace.single j (1 : ℝ)
  set m_fun : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
    (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
    (↑(japaneseBracket n ξ))⁻¹
  set g_cand := fun ξ => m_fun ξ * g ξ
  have hcand_bound : ∀ ξ, ‖g_cand ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := by
    intro ξ
    show ‖m_fun ξ * g ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    show ‖(2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
      (↑(japaneseBracket n ξ))⁻¹‖ ≤ 2 * Real.pi
    have hjb_pos := japaneseBracket_pos n ξ
    have h_inner_le : |@inner ℝ _ _ ξ ej| ≤ japaneseBracket n ξ := by
      have : |@inner ℝ _ _ ξ ej| ≤ ‖ξ‖ := by
        calc |@inner ℝ _ _ ξ ej|
          ≤ ‖ξ‖ * ‖ej‖ := abs_real_inner_le_norm _ _
          _ = ‖ξ‖ := by rw [PiLp.norm_single, norm_one, mul_one]
      calc |@inner ℝ _ _ ξ ej|
        ≤ ‖ξ‖ := this
        _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
          rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
          nlinarith [sq_nonneg ‖ξ‖]
        _ = japaneseBracket n ξ := rfl
    have hnorm_2piI : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
      rw [show (2 : ℂ) * ↑Real.pi * Complex.I = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg (by positivity)]
    rw [norm_mul, norm_mul, hnorm_2piI,
      Complex.norm_real, Real.norm_eq_abs,
      norm_inv, Complex.norm_real, Real.norm_of_nonneg hjb_pos.le]
    calc (2 * Real.pi) * |@inner ℝ _ _ ξ ej| * (japaneseBracket n ξ)⁻¹
      ≤ (2 * Real.pi) * japaneseBracket n ξ * (japaneseBracket n ξ)⁻¹ := by gcongr
      _ = 2 * Real.pi := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hjb_pos)]; ring
  have hcand_mem : MemLp g_cand 2 := by
    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖g_cand ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := hcand_bound
    have hm_cont : Continuous m_fun := by
      show Continuous (fun ξ => (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹)
      refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
      · exact Complex.continuous_ofReal.comp (Continuous.inner continuous_id continuous_const)
      · refine Continuous.inv₀ (Complex.continuous_ofReal.comp ?_) ?_
        · show Continuous (japaneseBracket n)
          unfold japaneseBracket; fun_prop
        · intro ξ; exact Complex.ofReal_ne_zero.mpr (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hm_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)
  have hcand_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
      ∫ ξ, (sobolevWeight n (s - 1) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ
    have heval : (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
      (2 * ↑Real.pi * Complex.I) *
      ((𝓕 u) (SchwartzMap.smulLeftCLM ℂ (fun ξ => (↑(@inner ℝ _ _ ξ ej) : ℂ)) φ)) := by
      change (𝓕 (LineDeriv.lineDerivOpCLM ℂ _ ej u)) φ = _
      rw [show (LineDeriv.lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) ej u) =
        LineDeriv.lineDerivOp ej u from rfl]
      have := TemperedDistribution.fourier_lineDerivOp_eq u ej
      rw [this]; rfl
    rw [heval, hg_eq]
    simp_rw [← smul_eq_mul (a := (2 * ↑Real.pi * Complex.I)), ← integral_smul]
    congr 1; ext ξ; simp only [smul_eq_mul]
    have htemp : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      (↑(@inner ℝ _ _ ξ ej) : ℂ)) :=
      (Complex.ofRealCLM.comp ((innerSL ℝ).flip ej)).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply htemp]; simp only [smul_eq_mul]
    have hjb_pos := japaneseBracket_pos n ξ
    have hjb_ne : (japaneseBracket n ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hjb_pos)
    simp only [sobolevWeight]
    have hws : ((japaneseBracket n ξ ^ (s - 1) : ℝ) : ℂ)⁻¹ *
      ((japaneseBracket n ξ : ℝ) : ℂ)⁻¹ =
      ((japaneseBracket n ξ ^ s : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        ← Complex.ofReal_inv]
      congr 1
      rw [← Real.rpow_neg hjb_pos.le, ← Real.rpow_neg hjb_pos.le,
        show (japaneseBracket n ξ)⁻¹ = japaneseBracket n ξ ^ ((-1 : ℝ)) from
          (Real.rpow_neg_one (japaneseBracket n ξ)).symm,
        ← Real.rpow_add hjb_pos]
      congr 1; linarith
    rw [← hws]; ring
  exact ⟨g_cand, hcand_mem, hcand_eq, hcand_bound⟩
set_option maxHeartbeats 1600000 in

end DiffOpSobolev

namespace DiffOpSobolev

/--
[memHs_iteratedPartialDeriv_with_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma memHs_iteratedPartialDeriv_with_bound
  {n : ℕ}
  {s : ℝ}
  {j : Fin n}
  {k : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg_mem : MemLp g 2)
  (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
-- imply
  ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g_new 2 ∧ (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (iteratedPartialDerivDistrib n j k u)) φ = ∫ ξ, (sobolevWeight n (s - ↑k) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧ (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) ^ k * ‖g ξ‖) := by
-- proof
  induction k generalizing s u g with
  | zero =>
    refine ⟨g, hg_mem, ?_, ?_⟩
    · simp only [iteratedPartialDerivDistrib, Function.iterate_zero, id_eq,
      Nat.cast_zero, sub_zero]
      exact hg_eq
    · intro ξ; simp only [pow_zero, one_mul]; exact le_refl _
  | succ k ih =>
    obtain ⟨g_k, hg_k_mem, hg_k_eq, hg_k_bound⟩ := @ih s u g hg_mem hg_eq
    have hstep := memHs_distribDeriv_with_bound n j
      (iteratedPartialDerivDistrib n j k u) g_k hg_k_mem hg_k_eq
    obtain ⟨g_new, hg_new_mem, hg_new_eq, hg_new_bound⟩ := hstep
    refine ⟨g_new, hg_new_mem, ?_, ?_⟩
    ·
      intro φ
      simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp]
      have h := hg_new_eq φ
      convert h using 2
      push_cast; ring
    ·
      intro ξ
      calc ‖g_new ξ‖ ≤ (2 * Real.pi) * ‖g_k ξ‖ := hg_new_bound ξ
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) ^ k * ‖g ξ‖) :=
          mul_le_mul_of_nonneg_left (hg_k_bound ξ) (by positivity)
        _ = (2 * Real.pi) ^ (k + 1) * ‖g ξ‖ := by ring
set_option maxHeartbeats 1600000 in

end DiffOpSobolev

namespace DiffOpSobolev

/--
[memHs_foldr_with_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma memHs_foldr_with_bound
  {n : ℕ}
  {s : ℝ}
  {l : List (Fin n)}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg_mem : MemLp g 2)
  (hg_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ) :
-- imply
  ∃ g_new : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g_new 2 ∧ (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u)) φ = ∫ ξ, (sobolevWeight n (s - ↑(l.map (fun j => α j)).sum) ξ : ℂ)⁻¹ * g_new ξ * φ ξ) ∧ (∀ ξ, ‖g_new ξ‖ ≤ (2 * Real.pi) ^ (l.map (fun j => α j)).sum * ‖g ξ‖) := by
-- proof
  induction l generalizing s u g with
  | nil =>
    refine ⟨g, hg_mem, ?_, ?_⟩
    · simp only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.cast_zero, sub_zero]
      exact hg_eq
    · intro ξ; simp only [List.map_nil, List.sum_nil, pow_zero, one_mul]; exact le_refl _
  | cons j l ih =>
    obtain ⟨g_tail, hg_tail_mem, hg_tail_eq, hg_tail_bound⟩ := @ih s u g hg_mem hg_eq
    have hstep := memHs_iteratedPartialDeriv_with_bound n j (α j)
      (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u)
      g_tail hg_tail_mem hg_tail_eq
    obtain ⟨g_new, hg_new_mem, hg_new_eq, hg_new_bound⟩ := hstep
    refine ⟨g_new, hg_new_mem, ?_, ?_⟩
    ·
      intro φ
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      have h := hg_new_eq φ
      convert h using 2
      push_cast; ring
    ·
      intro ξ
      simp only [List.map_cons, List.sum_cons]
      calc ‖g_new ξ‖
        ≤ (2 * Real.pi) ^ (α j) * ‖g_tail ξ‖ := hg_new_bound ξ
        _ ≤ (2 * Real.pi) ^ (α j) * ((2 * Real.pi) ^ (l.map (fun j => α j)).sum * ‖g ξ‖) :=
          mul_le_mul_of_nonneg_left (hg_tail_bound ξ) (by positivity)
        _ = (2 * Real.pi) ^ (α j + (l.map (fun j => α j)).sum) * ‖g ξ‖ := by
          rw [pow_add]; ring
set_option maxHeartbeats 1600000 in

end DiffOpSobolev

namespace DiffOpSobolev

/--
[iteratedDistribDeriv_witness_ae_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma iteratedDistribDeriv_witness_ae_bound
  {n : ℕ}
  {m : ℝ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
  {g' : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg : MemLp g 2)
  (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ)
  (hg'_mem : MemLp g' 2)
  (hg'_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (iteratedDistribDeriv n α u)) φ = ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ) :
-- imply
  ∀ᵐ ξ ∂volume, ‖g' ξ‖ ≤ (2 * Real.pi) ^ (∑ i, α i) * ‖g ξ‖ := by
-- proof
  have hfoldr := memHs_foldr_with_bound n (List.finRange n) α u g hg hug
  obtain ⟨g_cand, hg_cand_mem, hg_cand_eq, hg_cand_bound⟩ := hfoldr
  have hsum : ((List.finRange n).map (fun j => α j)).sum = ∑ i, α i := by
    exact (Fin.sum_univ_def α).symm
  have hg_cand_eq' : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    (𝓕 (iteratedDistribDeriv n α u)) φ =
      ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ
    have h := hg_cand_eq φ
    simp only [iteratedDistribDeriv] at h ⊢
    exact h
  have hint_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
    ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ =
    ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g_cand ξ * φ ξ := by
    intro φ; rw [← hg'_eq φ, ← hg_cand_eq' φ]
  have hae : g' =ᵐ[volume] g_cand :=
    sobolev_witness_ae_unique n g' g_cand hg'_mem hg_cand_mem hint_eq
  have hg_cand_bound' : ∀ ξ, ‖g_cand ξ‖ ≤ (2 * Real.pi) ^ (∑ i, α i) * ‖g ξ‖ := by
    intro ξ
    have h := hg_cand_bound ξ
    rwa [hsum] at h
  exact hae.mono (fun ξ hξ => by rw [hξ]; exact hg_cand_bound' ξ)

end DiffOpSobolev

namespace DiffOpSobolev

/--
[multiIndexDeriv_memHs_norm_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma multiIndexDeriv_memHs_norm_bound
  {n : ℕ}
  {m : ℝ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {g : EuclideanSpace ℝ (Fin n) → ℂ}
  {g' : EuclideanSpace ℝ (Fin n) → ℂ}
-- given
  (hg : MemLp g 2)
  (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ)
  (hg'_mem : MemLp g' 2)
  (hg'_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (iteratedDistribDeriv n α u)) φ = ∫ ξ, (sobolevWeight n (m - ↑(∑ i, α i)) ξ : ℂ)⁻¹ * g' ξ * φ ξ) :
-- imply
  eLpNorm g' 2 volume ≤ ENNReal.ofReal ((2 * Real.pi) ^ (∑ i, α i)) * eLpNorm g 2 volume :=
-- proof
  eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (iteratedDistribDeriv_witness_ae_bound n α u g hg hug hg'_mem hg'_eq) 2

end DiffOpSobolev

namespace DiffOpSobolev

/--
[multiIndexDeriv_Hs_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma multiIndexDeriv_Hs_continuous
  {n : ℕ}
  {m : ℝ}
  {α : Fin n → ℕ} :
-- imply
  let s := m - ↑(∑ i, α i) ∃ C : ℝ, C > 0 ∧ ∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2) (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ), ∃ g' : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g' 2 ∧ (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (iteratedDistribDeriv n α u)) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g' ξ * φ ξ) ∧ eLpNorm g' 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume := by
-- proof
  intro s
  refine ⟨(2 * Real.pi) ^ (∑ i, α i), by positivity, ?_⟩
  intro u g hg hug
  have hu_memHs : MemHs n m u := ⟨g, hg, hug⟩
  have hderiv := memHs_iteratedDistribDeriv α u hu_memHs
  have hs : m - (↑(multiIndexOrder n α) : ℝ) = s := rfl
  rw [hs] at hderiv
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hderiv
  refine ⟨g', hg'_mem, ?_, ?_⟩
  · exact hg'_eq
  · exact multiIndexDeriv_memHs_norm_bound n α u g hg hug hg'_mem hg'_eq

end DiffOpSobolev

namespace DiffOpSobolev

/--
[iteratedDistribDeriv_memHs_and_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
lemma iteratedDistribDeriv_memHs_and_bounded
  {n : ℕ}
  {m : ℝ}
  {α : Fin n → ℕ} :
-- imply
  (∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)), MemHs n m u → MemHs n (m - ↑(∑ i, α i)) (iteratedDistribDeriv n α u)) ∧ (let s := m - ↑(∑ i, α i) ∃ C : ℝ, C > 0 ∧ ∀ (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (g : EuclideanSpace ℝ (Fin n) → ℂ) (hg : MemLp g 2) (hug : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 u) φ = ∫ ξ, (sobolevWeight n m ξ : ℂ)⁻¹ * g ξ * φ ξ), ∃ g' : EuclideanSpace ℝ (Fin n) → ℂ, MemLp g' 2 ∧ (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (𝓕 (iteratedDistribDeriv n α u)) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g' ξ * φ ξ) ∧ eLpNorm g' 2 volume ≤ ENNReal.ofReal C * eLpNorm g 2 volume) :=
-- proof
  ⟨fun u hu => multiIndexDeriv_memHs n α u hu,
    multiIndexDeriv_Hs_continuous n α⟩
end DiffOpSobolev


/--
[tailMultiIndexSum_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
private lemma tailMultiIndexSum_ge_eq
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {k : ℕ}
-- given
  (hk : n ≤ k) :
-- imply
  tailMultiIndexSum α k = 0 := by
-- proof
  apply DiffOpSobolev.tailMultiIndexSum_ge n α k hk

/--
[tailMultiIndexSum_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean)
-/
@[path]
private lemma tailMultiIndexSum_succ_eq
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {k : ℕ}
-- given
  (hk : k < n) :
-- imply
  tailMultiIndexSum α k = α ⟨k, hk⟩ + tailMultiIndexSum α (k + 1) := by
-- proof
  apply DiffOpSobolev.tailMultiIndexSum_succ n α k hk


-- created on 2026-10-23
