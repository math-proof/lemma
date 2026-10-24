import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Lemma.Definitions.Def_ModularForm_HeckeOperator
import Lemma.Int.P2MUtil
open Complex
open scoped ArithmeticFunction.sigma


/-- ported from external source -/

private lemma summable_sigma_mul_cexp_pow (z : UpperHalfPlane) :
  Summable fun n : ℕ => (σ 1 n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one 2 (UpperHalfPlane.norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ 1 n).trans_eq (by norm_num)

private lemma hasSum_sigma_succ_mul_cexp_pow (z : UpperHalfPlane) :
  HasSum (fun n : ℕ => (σ 1 (n + 1) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1))
    ((1 - EisensteinSeries.E2 z) / 24) := by
  have hs : Summable fun n : ℕ =>
      (σ 1 (n + 1) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow z)
  rw [hs.hasSum_iff, ← tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (σ 1 n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z) ^ n),
    EisensteinSeries.E2_eq_tsum_cexp z]
  ring

private lemma sigma_one_eq_sigmaPrimeTo_add (p n : ℕ) (hp : p ≠ 0) (hn : n ≠ 0) (hpn : p ∣ n) :
  σ 1 n = ModularCurve.sigmaPrimeTo p n + p * σ 1 (n / p) := by
  have hnp : n / p ≠ 0 := Nat.div_ne_zero_iff.mpr ⟨hp, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hpn⟩
  have himg : n.divisors.filter (fun d => p ∣ d) = (n / p).divisors.image (fun e => p * e) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    ·
      rintro ⟨⟨hdn, -⟩, e, rfl⟩
      exact ⟨e, ⟨(Nat.dvd_div_iff_mul_dvd hpn).mpr hdn, hnp⟩, rfl⟩
    ·
      rintro ⟨e, ⟨hednp, -⟩, rfl⟩
      exact ⟨⟨(Nat.dvd_div_iff_mul_dvd hpn).mp hednp, hn⟩, ⟨e, rfl⟩⟩
  have hinj : ∀ x ∈ (n / p).divisors, ∀ y ∈ (n / p).divisors, p * x = p * y → x = y :=
    fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h
  have hσ : σ 1 n = ∑ d ∈ n.divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  have hσ' : σ 1 (n / p) = ∑ d ∈ (n / p).divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  rw [hσ, hσ', ← Finset.sum_filter_add_sum_filter_not n.divisors (fun d => ¬ p ∣ d)]
  have hrw : n.divisors.filter (fun d => ¬ ¬ p ∣ d) = n.divisors.filter (fun d => p ∣ d) := by
    simp
  rw [hrw, himg, Finset.sum_image hinj, ← Finset.mul_sum]
  simp only [ModularCurve.sigmaPrimeTo]

private lemma sigmaPrimeTo_eq_sigma_one (p n : ℕ) (hpn : ¬ p ∣ n) :
  ModularCurve.sigmaPrimeTo p n = σ 1 n := by
  simp only [ArithmeticFunction.sigma_one_apply, ModularCurve.sigmaPrimeTo]
  congr 1
  exact Finset.filter_true_of_mem fun d hd hpd =>
    hpn (hpd.trans (Nat.mem_divisors.mp hd).1)

private lemma hasSum_zero_extension_of_dvd {p : ℕ} (hp : p ≠ 0) (c : ℕ → ℂ) (q : ℂ) (s : ℂ)
  (h : HasSum (fun n : ℕ => c (n + 1) * q ^ (p * (n + 1))) s) :
  HasSum (fun n : ℕ => if p ∣ (n + 1) then c ((n + 1) / p) * q ^ (n + 1) else 0) s := by
  have hg : Function.Injective (fun n : ℕ => p * n + (p - 1)) := by
    intro a b hab
    have hab' : p * a + (p - 1) = p * b + (p - 1) := hab
    have h1 : p * a = p * b := by omega
    refine Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) h1
  have hvanish : ∀ x, x ∉ Set.range (fun n : ℕ => p * n + (p - 1)) →
      (if p ∣ (x + 1) then c ((x + 1) / p) * q ^ (x + 1) else 0) = 0 := by
    intro x hx
    rw [ite_eq_right]
    rintro ⟨m, hm⟩
    apply hx
    rcases m with - | m'
    · exact absurd hm (by omega)
    ·
      refine ⟨m', ?_⟩
      rw [Nat.mul_succ] at hm
      show p * m' + (p - 1) = x
      omega
  refine (Function.Injective.hasSum_iff hg hvanish).mp ?_
  have hcomp : ((fun n : ℕ => if p ∣ (n + 1) then c ((n + 1) / p) * q ^ (n + 1) else 0) ∘
      (fun n : ℕ => p * n + (p - 1))) = fun n : ℕ => c (n + 1) * q ^ (p * (n + 1)) := by
    funext n
    have h1 : p * n + (p - 1) + 1 = p * (n + 1) := by
      rw [Nat.mul_succ]
      omega
    simp only [Function.comp_apply, h1]
    rw [ite_eq_left (dvd_mul_right p (n + 1)), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
  rwa [hcomp]
p2m_open_scoped "ModularCurve" in

private lemma ModularCurve.hasSum_eisensteinTwoCoeff_mul_cexp_pow (p : ℕ) [NeZero p]
  (τ : UpperHalfPlane) :
  HasSum (fun n : ℕ => (ModularCurve.eisensteinTwoCoeff p n : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * τ) ^ n)
    ((p : ℂ) * EisensteinSeries.E2 (ModularForm.heckeDiagMatrix p • τ) -
      EisensteinSeries.E2 τ) := by
  have hp : p ≠ 0 := NeZero.ne p
  have hsmul : ((ModularForm.heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ) = (p : ℂ) * (τ : ℂ) :=
    ModularForm.coe_heckeDiagMatrix_smul hp τ
  have hqp : Complex.exp (2 * Real.pi * Complex.I *
        ((ModularForm.heckeDiagMatrix p • τ : UpperHalfPlane) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ p := by
    rw [hsmul, show 2 * (Real.pi : ℂ) * Complex.I * ((p : ℂ) * (τ : ℂ)) =
        (p : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) by ring, Complex.exp_nat_mul]
  have h₁ := (hasSum_sigma_succ_mul_cexp_pow τ).mul_left 24
  have h₂ := (hasSum_sigma_succ_mul_cexp_pow
      (ModularForm.heckeDiagMatrix p • τ)).mul_left (24 * (p : ℂ))
  simp only [hqp, ← pow_mul, ← mul_assoc] at h₂
  have h₂' := hasSum_zero_extension_of_dvd hp
    (fun m : ℕ => 24 * (p : ℂ) * (σ 1 m : ℂ))
    (Complex.exp (2 * Real.pi * Complex.I * τ)) _ h₂
  rw [← hasSum_nat_add_iff' 1]
  convert h₁.sub h₂' using 1
  ·
    funext n
    by_cases hdvd : p ∣ (n + 1)
    ·
      simp only [ModularCurve.eisensteinTwoCoeff_of_ne_zero p
        (show n + 1 ≠ 0 from Nat.succ_ne_zero n), ite_eq_left hdvd]
      have hsplit : (σ 1 (n + 1) : ℂ) = (ModularCurve.sigmaPrimeTo p (n + 1) : ℂ) +
          (p : ℂ) * (σ 1 ((n + 1) / p) : ℂ) := by
        exact_mod_cast sigma_one_eq_sigmaPrimeTo_add p (n + 1) hp
          (Nat.succ_ne_zero n) hdvd
      rw [hsplit]
      push_cast
      ring
    ·
      simp only [ModularCurve.eisensteinTwoCoeff_of_ne_zero p
        (show n + 1 ≠ 0 from Nat.succ_ne_zero n), ite_eq_right hdvd, sub_zero,
        sigmaPrimeTo_eq_sigma_one p (n + 1) hdvd]
      push_cast
      ring
  ·
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      ModularCurve.eisensteinTwoCoeff_zero]
    push_cast
    ring
@[path]
private lemma main
  :
-- imply
  ∀ (p : ℕ) [NeZero p] (τ : UpperHalfPlane), HasSum (fun n : ℕ => (ModularCurve.eisensteinTwoCoeff p n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) ((p : ℂ) * EisensteinSeries.E2 (ModularForm.heckeDiagMatrix p • τ) - EisensteinSeries.E2 τ) :=
-- proof
  @ModularCurve.hasSum_eisensteinTwoCoeff_mul_cexp_pow


-- created on 2026-10-23
