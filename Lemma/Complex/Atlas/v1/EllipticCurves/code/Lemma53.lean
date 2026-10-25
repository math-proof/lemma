import Mathlib
import sympy.Basic
import Def.v1.Atlas.EllipticCurves.code.IsogenyKernels.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IsogenyKernels
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
open Polynomial


/--
[Polynomial.derivative_eq_zero_of_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma Polynomial.derivative_eq_zero_of_sq
  [Field k]
  {t : k[X]}
-- given
  (hp2 : (2 : k) ≠ 0)
  (ht : t ≠ 0)
  (h : derivative (t ^ 2) = 0) :
-- imply
  derivative t = 0 := by
-- proof
  have h1 : C 2 * t * derivative t = 0 := by
    have h2 : derivative (t ^ 2) = C 2 * t * derivative t := by
      rw [derivative_pow]; ring_nf
    rw [h2] at h; exact h
  have h2_ne : (C (2 : k) : k[X]) ≠ 0 := by rwa [Ne, C_eq_zero]
  obtain h2 | h3 := mul_eq_zero.mp h1
  · rcases mul_eq_zero.mp h2 with h4 | h5
    · exact absurd h4 h2_ne
    · exact absurd h5 ht
  · exact h3

/--
[wronskian_from_curve_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma wronskian_from_curve_eq
  [Field k]
  {v s t f₁ w : k[X]}
-- given
  (hv_ne : v ≠ 0)
  (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
  (hv' : derivative v = 0)
  (hw' : derivative w = 0) :
-- imply
  (s ^ 2 * f₁).wronskian (t ^ 2) = 0 := by
-- proof
  have hcurve2 : v ^ 3 * (s ^ 2 * f₁) = t ^ 2 * w := by linear_combination hcurve
  have lhs_d : derivative (v ^ 3 * (s ^ 2 * f₁)) = v ^ 3 * derivative (s ^ 2 * f₁) := by
    rw [derivative_mul, derivative_pow, hv']; ring
  have rhs_d : derivative (t ^ 2 * w) = derivative (t ^ 2) * w := by
    rw [derivative_mul, hw', mul_zero, add_zero]
  have h_diff : v ^ 3 * derivative (s ^ 2 * f₁) = derivative (t ^ 2) * w := by
    have h := congr_arg derivative hcurve2; rw [lhs_d, rhs_d] at h; exact h
  have key : v ^ 3 * (s ^ 2 * f₁ * derivative (t ^ 2) - derivative (s ^ 2 * f₁) * t ^ 2) = 0 := by
    linear_combination derivative (t ^ 2) * hcurve2 - t ^ 2 * h_diff
  simp only [wronskian]
  exact or_iff_not_imp_left.mp (mul_eq_zero.mp key) (pow_ne_zero _ hv_ne)

/--
[lemma_5_3_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma lemma_5_3_x
  [Field k]
  {p : ℕ}
  [CharP k p]
  {u v : k[X]}
-- given
  (hp : p ≠ 0)
  (hcop : IsCoprime u v)
  (hinsep : derivative u * v - u * derivative v = 0) :
-- imply
  ∃ (f g : k[X]), expand k p f = u ∧ expand k p g = v := by
-- proof
  have hwronskian : u.wronskian v = 0 := by
    simp only [wronskian]; linear_combination -hinsep
  have ⟨hu', hv'⟩ := hcop.wronskian_eq_zero_iff.mp hwronskian
  exact ⟨contract p u, contract p v, expand_contract p hu' hp, expand_contract p hv' hp⟩

/--
[coprime_s2f1_t2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma coprime_s2f1_t2
  [Field k]
  {s t f₁ : k[X]}
-- given
  (hcop_st : IsCoprime s t)
  (hcop_ft : IsCoprime f₁ t) :
-- imply
  IsCoprime (s ^ 2 * f₁) (t ^ 2) :=
-- proof
  (hcop_st.pow_left.pow_right).mul_left (hcop_ft.pow_right)

/--
[dvd_of_dvd_mul_isUnit_poly](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma dvd_of_dvd_mul_isUnit_poly
  [Field k]
  {a b c : k[X]}
-- given
  (hu : IsUnit a)
  (h : c ∣ a * b) :
-- imply
  c ∣ b := by
-- proof
  obtain ⟨d, hd⟩; rcases hu with ⟨u, rfl⟩ := h
  exact ⟨↑u⁻¹ * d, by
    rw [show b = ↑u⁻¹ * (↑u * b) from by simp [Units.inv_mul_cancel_left], hd]; ring⟩

/--
[sep_dvd_of_deriv_sq_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma sep_dvd_of_deriv_sq_mul_pow
  [Field k]
  {r f₁ : k[X]}
  {m : ℕ}
-- given
  (hm : m > 0)
  (hCm : (m : k) ≠ 0)
  (hf₁_sep : f₁.Separable)
  (h_deriv : derivative (r ^ 2 * f₁ ^ m) = 0) :
-- imply
  f₁ ∣ r := by
-- proof
  have hf₁_sf := hf₁_sep.squarefree
  have hf₁_ne := hf₁_sf.ne_zero
  have h1 : derivative (r ^ 2) * f₁ ^ m + r ^ 2 * derivative (f₁ ^ m) = 0 := by
    rw [← derivative_mul]; exact h_deriv
  rw [derivative_pow f₁ m] at h1
  have h2 : f₁ ^ (m - 1) * (derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁) = 0 := by
    have : f₁ ^ m = f₁ * f₁ ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this] at h1
    have eq : derivative (r ^ 2) * (f₁ * f₁ ^ (m - 1)) +
      r ^ 2 * (C (↑m : k) * f₁ ^ (m - 1) * derivative f₁) =
      f₁ ^ (m - 1) * (derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁) := by ring
    rw [eq] at h1; exact h1
  have h3 : derivative (r ^ 2) * f₁ + C (↑m : k) * r ^ 2 * derivative f₁ = 0 :=
    or_iff_not_imp_left.mp (mul_eq_zero.mp h2) (pow_ne_zero _ hf₁_ne)
  have h4 : f₁ ∣ C (↑m : k) * r ^ 2 := hf₁_sep.dvd_of_dvd_mul_right (by
    rw [(neg_eq_of_add_eq_zero_right h3).symm]; exact dvd_neg.mpr (dvd_mul_left f₁ _))
  exact (hf₁_sf.dvd_pow_iff_dvd (by norm_num : (2 : ℕ) ≠ 0)).mp
    (dvd_of_dvd_mul_isUnit_poly
      (by rw [Polynomial.isUnit_C, isUnit_iff_ne_zero]; exact hCm) h4)

/--
[insep_y_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma insep_y_factor
  [Field k]
  {p : ℕ}
  [CharP k p]
  {s f₁ : k[X]}
-- given
  (hp : p ≠ 0)
  (hp2 : (2 : k) ≠ 0)
  (hs : s ≠ 0)
  (hf₁_sep : f₁.Separable)
  (h_deriv : derivative (s ^ 2 * f₁) = 0) :
-- imply
  ∃ (g₂ : k[X]), s ^ 2 * f₁ = (expand k p g₂) ^ 2 * f₁ ^ p := by
-- proof
  have hf₁_ne := hf₁_sep.squarefree.ne_zero
  have hp_prime : Nat.Prime p := by
    obtain h | h; exact h; exact absurd h hp := CharP.char_is_prime_or_zero k p
  have hp2n : p ≠ 2 := by intro h; subst h; exact hp2 (CharP.cast_eq_zero k 2)
  have key : ∀ n : ℕ, n ≤ (p - 1) / 2 →
    ∃ r : k[X], s = f₁ ^ n * r ∧
      derivative (r ^ 2 * f₁ ^ (2 * n + 1)) = 0 ∧ r ≠ 0 := by
    intro n hn
    induction n with
    | zero => exact ⟨s, by simp, by simpa using h_deriv, hs⟩
    | succ n ih =>
      obtain ⟨r, hrs, hrd, hr_ne⟩ := ih (le_of_lt (Nat.lt_of_succ_le hn))
      have h_lt : 2 * n + 1 < p := by
        have := Nat.lt_of_succ_le hn; omega
      obtain ⟨r', rfl⟩ := sep_dvd_of_deriv_sq_mul_pow (by omega) (by
        intro h; rw [CharP.cast_eq_zero_iff k p] at h
        exact Nat.not_dvd_of_pos_of_lt (by omega) h_lt h) hf₁_sep hrd
      refine ⟨r', by rw [hrs, pow_succ, mul_assoc], ?_,
        by intro h; apply hr_ne; rw [h, mul_zero]⟩
      rwa [show (f₁ * r') ^ 2 * f₁ ^ (2 * n + 1) =
        r' ^ 2 * f₁ ^ (2 * (n + 1) + 1) from by ring_nf] at hrd
  obtain ⟨r, hrs, hrd, hr_ne⟩ := key ((p - 1) / 2) le_rfl
  have h_exp : 2 * ((p - 1) / 2) + 1 = p := by
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hp_prime hp2n; omega
  rw [h_exp] at hrd
  have h_dr2_zero : derivative (r ^ 2) = 0 := by
    have h := hrd
    rw [derivative_mul, show derivative (f₁ ^ p) = 0 from by
      rw [derivative_pow]; simp,
      mul_zero, add_zero] at h
    exact or_iff_not_imp_right.mp (mul_eq_zero.mp h) (pow_ne_zero _ hf₁_ne)
  have hr'_zero := Polynomial.derivative_eq_zero_of_sq hp2 hr_ne h_dr2_zero
  refine ⟨contract p r, ?_⟩
  calc s ^ 2 * f₁
    = (f₁ ^ ((p - 1) / 2) * r) ^ 2 * f₁ := by rw [hrs]
    _ = r ^ 2 * f₁ ^ (2 * ((p - 1) / 2) + 1) := by ring
    _ = r ^ 2 * f₁ ^ p := by rw [h_exp]
    _ = (expand k p (contract p r)) ^ 2 * f₁ ^ p := by rw [expand_contract p hr'_zero hp]

/--
[lemma_5_3_y_deriv_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma lemma_5_3_y_deriv_t
  [Field k]
  {v s t f₁ w : k[X]}
-- given
  (hp2 : (2 : k) ≠ 0)
  (hv_ne : v ≠ 0)
  (ht_ne : t ≠ 0)
  (hcop_st : IsCoprime s t)
  (hcop_ft : IsCoprime f₁ t)
  (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
  (hv' : derivative v = 0)
  (hw' : derivative w = 0) :
-- imply
  derivative t = 0 := by
-- proof
  have hwron := wronskian_from_curve_eq hv_ne hcurve hv' hw'
  have hcop := coprime_s2f1_t2 hcop_st hcop_ft
  have ht2' := (hcop.wronskian_eq_zero_iff.mp hwron).2
  exact Polynomial.derivative_eq_zero_of_sq hp2 ht_ne ht2'

/--
[lemma_5_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Lemma53.lean)
-/
@[path]
lemma lemma_5_3
  [Field k]
  {p : ℕ}
  [CharP k p]
  {u v s t f₁ w : k[X]}
-- given
  (hp : p ≠ 0)
  (hp2 : (2 : k) ≠ 0)
  (hcop_uv : IsCoprime u v)
  (hcop_st : IsCoprime s t)
  (hcop_ft : IsCoprime f₁ t)
  (hv_ne : v ≠ 0)
  (ht_ne : t ≠ 0)
  (hs_ne : s ≠ 0)
  (hf₁_sep : f₁.Separable)
  (hinsep : derivative u * v - u * derivative v = 0)
  (hcurve : v ^ 3 * s ^ 2 * f₁ = t ^ 2 * w)
  (hw' : derivative w = 0) :
-- imply
  (∃ (f g : k[X]), expand k p f = u ∧ expand k p g = v) ∧ (∃ (t₀ : k[X]), expand k p t₀ = t) ∧ (∃ (g₂ : k[X]), s ^ 2 * f₁ = (expand k p g₂) ^ 2 * f₁ ^ p) := by
-- proof
  have hwronskian : u.wronskian v = 0 := by
    simp only [wronskian]; linear_combination -hinsep
  have ⟨hu', hv'⟩ := hcop_uv.wronskian_eq_zero_iff.mp hwronskian
  refine ⟨⟨contract p u, contract p v, expand_contract p hu' hp, expand_contract p hv' hp⟩,
    ?_, ?_⟩
  · have ht' : derivative t = 0 :=
    lemma_5_3_y_deriv_t hp2 hv_ne ht_ne hcop_st hcop_ft hcurve hv' hw'
    exact ⟨contract p t, expand_contract p ht' hp⟩
  ·
    have hwron := wronskian_from_curve_eq hv_ne hcurve hv' hw'
    have hcop := coprime_s2f1_t2 hcop_st hcop_ft
    have hs2f1' := (hcop.wronskian_eq_zero_iff.mp hwron).1
    exact insep_y_factor hp hp2 hs_ne hf₁_sep hs2f1'


-- created on 2026-10-23
