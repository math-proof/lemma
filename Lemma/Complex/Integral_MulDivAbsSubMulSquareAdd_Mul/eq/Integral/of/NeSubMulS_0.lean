import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


private lemma volume_affine_zero (p q : ℝ) (h : p ≠ 0 ∨ q ≠ 0) : volume {x : ℝ | p + x * q = 0} = 0 := by
  obtain hq | hq := eq_or_ne q 0
  ·
    have hp : p ≠ 0 := h.resolve_right (not_not.mpr hq)
    refine measure_mono_null (fun x hx => (hp (by simpa [hq] using hx)).elim) measure_empty
  ·
    refine measure_mono_null (fun x hx => ?_) (measure_singleton (-p / q))
    simp only [Set.mem_ofPred_eq] at hx
    rw [Set.mem_singleton_iff, eq_div_iff hq]
    linarith

private lemma helper_main (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) (G : ℝ → ℂ) :
  ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
    = ∫ u : ℝ, G u := by
  set s : Set ℝ := {x | a + x * c ≠ 0} with hs_def
  set t : Set ℝ := {u | d - u * c ≠ 0} with ht_def
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hdet; rw [h.1, h.2]; ring
  have hdc : d ≠ 0 ∨ -c ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not, neg_eq_zero] at h
    apply hdet; rw [h.1, h.2]; ring
  have hs : MeasurableSet s := (isOpen_ne_fun (by fun_prop) continuous_const).measurableSet
  have hderiv : ∀ x ∈ s, HasDerivWithinAt (fun y : ℝ => (b + y * d) / (a + y * c))
    ((a * d - b * c) / (a + x * c) ^ 2) s x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => b + y * d) d x := by
      simpa using ((hasDerivAt_id x).mul_const d).const_add b
    have h2 : HasDerivAt (fun y : ℝ => a + y * c) c x := by
      simpa using ((hasDerivAt_id x).mul_const c).const_add a
    have h3 := h1.div h2 hx
    refine (h3.congr_deriv ?_).hasDerivWithinAt
    congr 1; ring
  have hinj : Set.InjOn (fun y : ℝ => (b + y * d) / (a + y * c)) s := by
    intro x hx y hy hxy
    dsimp only at hxy
    rw [div_eq_div_iff hx hy] at hxy
    have h0 : (x - y) * (a * d - b * c) = 0 := by linear_combination hxy
    obtain h | h := mul_eq_zero.mp h0
    · linarith
    · exact absurd h hdet
  have himage : (fun y : ℝ => (b + y * d) / (a + y * c)) '' s = t := by
    ext u
    constructor
    ·
      rintro ⟨x, hx, rfl⟩
      change d - (b + x * d) / (a + x * c) * c ≠ 0
      have hx' : a + x * c ≠ 0 := hx
      rw [show d - (b + x * d) / (a + x * c) * c = (a * d - b * c) / (a + x * c) by field_simp; ring]
      exact div_ne_zero hdet hx'
    ·
      intro hu
      change d - u * c ≠ 0 at hu
      have hden : a + (u * a - b) / (d - u * c) * c ≠ 0 := by
        rw [show a + (u * a - b) / (d - u * c) * c = (a * d - b * c) / (d - u * c) by field_simp; ring]
        exact div_ne_zero hdet hu
      refine ⟨(u * a - b) / (d - u * c), hden, ?_⟩
      change (b + (u * a - b) / (d - u * c) * d) / (a + (u * a - b) / (d - u * c) * c) = u
      rw [div_eq_iff hden]
      field_simp
      ring
  have key := integral_image_eq_integral_abs_deriv_smul hs hderiv hinj G
  rw [himage] at key
  have hs_ae : s =ᵐ[volume] Set.univ := by
    rw [ae_eq_univ, hs_def, show {x : ℝ | a + x * c ≠ 0}ᶜ = {x | a + x * c = 0} by ext; simp]
    exact volume_affine_zero a c hac
  have ht_ae : t =ᵐ[volume] Set.univ := by
    have hcompl : {u : ℝ | d - u * c ≠ 0}ᶜ = {u | d + u * (-c) = 0} := by
      ext u; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]; constructor <;> intro h <;> linarith
    rw [ae_eq_univ, ht_def, hcompl]
    exact volume_affine_zero d (-c) hdc
  rw [setIntegral_congr_set ht_ae, setIntegral_congr_set hs_ae, Measure.restrict_univ] at key
  rw [key]
  congr 1
  funext x
  rw [Complex.real_smul, abs_div, abs_of_nonneg (sq_nonneg (a + x * c))]
/--
[MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_integral_abs_det_div_sq_mul_comp_moebius_real.lean)
-/
@[path]
private lemma main
  {a b c d : ℝ}
  {G : ℝ → ℂ}
-- given
  (hdet : a * d - b * c ≠ 0) :
-- imply
  ∫ x : ℝ, ((|a * d - b * c| / (a + x * c) ^ 2 : ℝ) : ℂ) * G ((b + x * d) / (a + x * c))
    = ∫ u : ℝ, G u := helper_main a b c d hdet G
-- proof


-- created on 2026-10-23
