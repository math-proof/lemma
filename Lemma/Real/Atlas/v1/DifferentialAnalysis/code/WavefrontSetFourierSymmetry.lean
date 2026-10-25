import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontSetFourierSymmetry
open MeasureTheory WavefrontSet
open scoped SchwartzMap FourierTransform


namespace WavefrontSet

/--
[isSmoothNear_fourier_smulLeftCLM_compactlySupported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma isSmoothNear_fourier_smulLeftCLM_compactlySupported
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {φ : ConeSupport.E n → ℂ}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hφ : ContDiff ℝ ↑(⊤ : ℕ∞) φ)
  (hφc : HasCompactSupport φ) :
-- imply
  ConeSupport.IsSmoothNear (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) x := by
-- proof
  obtain ⟨f, hf⟩ := ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ hφc u
  rw [hf]
  exact ConeSupport.isSmoothNear_schwartzConvolution (𝓕 u) f x

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_fourier_compactlySupported_interior](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma not_mem_css_fourier_compactlySupported_interior
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {φ : ConeSupport.E n → ℂ}
  {q : ClosedBall n}
-- given
  (hφ : ContDiff ℝ ↑(⊤ : ℕ∞) φ)
  (hφc : HasCompactSupport φ)
  (hq : ‖q.val‖ < 1) :
-- imply
  q ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) := by
-- proof
  simp only [Css, Set.mem_setOf_eq, dif_neg (ne_of_lt hq)]
  simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]
  exact isSmoothNear_fourier_smulLeftCLM_compactlySupported u φ hφ hφc _
set_option maxHeartbeats 400000 in

end WavefrontSet

namespace WavefrontSet

/--
[wfsc_subset_boundaryProd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma wfsc_subset_boundaryProd
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  WFsc u ⊆ BoundaryProd n := by
-- proof
  intro ⟨p, q⟩ hmem
  simp only [BoundaryProd, Set.mem_setOf_eq]
  by_contra h
  push Not at h
  obtain ⟨hp_ne, hq_ne⟩ := h
  have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp_ne
  have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq_ne
  simp only [WFsc, Set.mem_setOf_eq] at hmem
  apply hmem
  rw [dif_neg hp_ne]
  set x₀ := p.toEuclidean hp_lt
  set χ : ContDiffBump x₀ := ⟨1, 2, one_pos, by norm_num⟩
  set φ := fun x => Complex.ofReal (χ x) with hφ_def
  have hφ_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) φ := by
    rw [contDiff_infty]; intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hφ_compact : HasCompactSupport φ :=
    χ.hasCompactSupport.comp_left Complex.ofReal_zero
  refine ⟨φ, hφ_smooth, hφ_compact, ?_, ?_⟩
  ·
    have h1 : χ x₀ = 1 :=
      χ.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt χ.rIn_pos))
    simp only [hφ_def, h1, Complex.ofReal_one, ne_eq]
    exact one_ne_zero
  ·
    exact not_mem_css_fourier_compactlySupported_interior u φ hφ_smooth hφ_compact q hq_lt

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_iff_neg_not_mem_css_fourier_fourier'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma not_mem_css_iff_neg_not_mem_css_fourier_fourier'
  {n : ℕ}
  {u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : ClosedBall n} :
-- imply
  p ∉ Css u₁ ↔ (-p) ∉ Css (𝓕 (𝓕 u₁)) :=
-- proof
  not_mem_css_iff_neg_not_mem_css_fourier_fourier u₁ p

end WavefrontSet

namespace WavefrontSet

/--
[mem_wfsc_fourier_fourier_iff_neg_mem_wfsc'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma mem_wfsc_fourier_fourier_iff_neg_mem_wfsc'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {a b : ClosedBall n} :
-- imply
  (a, b) ∈ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∈ WFsc u := by
-- proof
  by_cases hab : (a, b) ∈ BoundaryProd n
  ·
    have hnab : (-a, -b) ∈ BoundaryProd n := by
      simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hab ⊢
      exact hab
    rw [show ((a, b) ∈ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∈ WFsc u) ↔
      ((a, b) ∉ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∉ WFsc u) from not_iff_not.symm]
    rw [not_mem_wfsc_iff_exists_css_decomp hab,
      not_mem_wfsc_iff_exists_css_decomp hnab]
    constructor
    ·
      rintro ⟨v₁, v₂, hdecomp, ha_v₁, hb_fv₂⟩
      refine ⟨𝓕⁻ (𝓕⁻ v₁), 𝓕⁻ (𝓕⁻ v₂), ?_, ?_, ?_⟩
      ·
        have : 𝓕 (𝓕 u) = v₁ + v₂ := hdecomp
        have h1 : u = 𝓕⁻ (𝓕⁻ (𝓕 (𝓕 u))) := by simp
        rw [h1, this]
        simp
      ·
        rw [show v₁ = 𝓕 (𝓕 (𝓕⁻ (𝓕⁻ v₁))) from by simp] at ha_v₁
        exact (not_mem_css_iff_neg_not_mem_css_fourier_fourier' (𝓕⁻ (𝓕⁻ v₁)) (-a)).mpr
          (by simp only [ClosedBall.neg_neg]; exact ha_v₁)
      ·
        rw [show 𝓕 (𝓕⁻ (𝓕⁻ v₂)) = 𝓕⁻ v₂ from by simp]
        exact (not_mem_css_iff_neg_not_mem_css_fourier_fourier' (𝓕⁻ v₂) (-b)).mpr
          (by simp only [ClosedBall.neg_neg, show 𝓕 (𝓕 (𝓕⁻ v₂)) = 𝓕 v₂ from by simp]
            exact hb_fv₂)
    ·
      rintro ⟨w₁, w₂, hdecomp, hna_w₁, hnb_fw₂⟩
      refine ⟨𝓕 (𝓕 w₁), 𝓕 (𝓕 w₂), ?_, ?_, ?_⟩
      ·
        rw [hdecomp]
        simp [FourierTransform.fourier_add]
      ·
        have := (not_mem_css_iff_neg_not_mem_css_fourier_fourier' w₁ (-a)).mp hna_w₁
        simp only [ClosedBall.neg_neg] at this
        exact this
      ·
        have := (not_mem_css_iff_neg_not_mem_css_fourier_fourier' (𝓕 w₂) (-b)).mp hnb_fw₂
        simp only [ClosedBall.neg_neg] at this
        exact this
  ·
    have hnab : (-a, -b) ∉ BoundaryProd n := by
      simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hab ⊢
      exact hab
    constructor
    · intro h; exact absurd (wfsc_subset_boundaryProd (𝓕 (𝓕 u)) h) hab
    · intro h; exact absurd (wfsc_subset_boundaryProd u h) hnab

end WavefrontSet

namespace WavefrontSet

/--
[boundaryProd_swap_neg'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma boundaryProd_swap_neg'
  {n : ℕ}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (q, -p) ∈ BoundaryProd n := by
-- proof
  simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hpq ⊢
  exact hpq.symm

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_wfsc_of_not_mem_wfsc_fourier'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma not_mem_wfsc_of_not_mem_wfsc_fourier'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n)
  (h : (p, q) ∉ WFsc u) :
-- imply
  (q, -p) ∉ WFsc (𝓕 u) := by
-- proof
  rw [not_mem_wfsc_iff_exists_css_decomp hpq] at h
  obtain ⟨u₁, u₂, hudecomp, hp_u1, hq_fu2⟩ := h
  rw [not_mem_wfsc_iff_exists_css_decomp (boundaryProd_swap_neg' hpq)]
  exact ⟨𝓕 u₂, 𝓕 u₁,
    by rw [hudecomp, FourierTransform.fourier_add]; exact add_comm _ _,
    hq_fu2,
    (not_mem_css_iff_neg_not_mem_css_fourier_fourier' u₁ p).mp hp_u1⟩

end WavefrontSet

namespace WavefrontSet

/--
[mem_wfsc_iff_swap_neg_mem_wfsc_fourier'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetFourierSymmetry.lean)
-/
@[path]
lemma mem_wfsc_iff_swap_neg_mem_wfsc_fourier'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n} :
-- imply
  (p, q) ∈ WFsc u ↔ (q, -p) ∈ WFsc (𝓕 u) := by
-- proof
  constructor
  · intro hmem
    by_contra habs
    have hpq : (p, q) ∈ BoundaryProd n := wfsc_subset_boundaryProd u hmem
    have hbnd : (q, -p) ∈ BoundaryProd n := boundaryProd_swap_neg' hpq
    have h1 : (-p, -q) ∉ WFsc (𝓕 (𝓕 u)) :=
      not_mem_wfsc_of_not_mem_wfsc_fourier' (𝓕 u) hbnd habs
    have h2 : (-p, -q) ∈ WFsc (𝓕 (𝓕 u)) := by
      rw [mem_wfsc_fourier_fourier_iff_neg_mem_wfsc' u (-p) (-q)]
      simp only [ClosedBall.neg_neg]
      exact hmem
    exact h1 h2
  · intro hmem
    by_contra habs
    have hqp : (q, -p) ∈ BoundaryProd n := wfsc_subset_boundaryProd (𝓕 u) hmem
    have hpq : (p, q) ∈ BoundaryProd n := by
      simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hqp ⊢
      exact hqp.symm
    exact absurd hmem (not_mem_wfsc_of_not_mem_wfsc_fourier' u hpq habs)
end WavefrontSet



-- created on 2026-10-23
