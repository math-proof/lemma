import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.ECM
open Nat Finset


/--
[shortWeierstrass_Δ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
`-16 (4 a³ + 27 b²)`. -/
lemma shortWeierstrass_Δ {R : Type*} [CommRing R] (a b : R) :
  (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
  simp only [shortWeierstrass, ecmDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/--
[ECMCurveParams.point_on_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ECMCurveParams.point_on_curve
  {params : ECMCurveParams} :
-- imply
  WeierstrassCurve.Affine.Equation params.curve params.x₀ params.y₀ := by
-- proof
  unfold WeierstrassCurve.Affine.Equation Polynomial.evalEval
  simp only [ECMCurveParams.curve, shortWeierstrass, ECMCurveParams.b,
    WeierstrassCurve.Affine.polynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/--
[ecmSmoothExponent_bound_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmSmoothExponent_bound_le
  {ℓ M : ℕ}
-- given
  (_hℓ : 1 < ℓ) :
-- imply
  ℓ ^ (ecmSmoothExponent ℓ M - 1) ≤ (Nat.sqrt M + 1) ^ 2 := by
-- proof
  simp only [ecmSmoothExponent, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self ℓ (by positivity)

/--
[ecmSmoothExponent_bound_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmSmoothExponent_bound_lt
  {ℓ M : ℕ}
-- given
  (hℓ : 1 < ℓ) :
-- imply
  (Nat.sqrt M + 1) ^ 2 < ℓ ^ ecmSmoothExponent ℓ M := by
-- proof
  simp only [ecmSmoothExponent]
  exact Nat.lt_pow_succ_log_self hℓ _

/--
[ecmSmoothScalar_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmSmoothScalar_pos
  {B M : ℕ} :
-- imply
  0 < ecmSmoothScalar B M := by
-- proof
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/--
[ecmPartialScalar_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmPartialScalar_pos
  {ℓ₁ M : ℕ} :
-- imply
  0 < ecmPartialScalar ℓ₁ M := by
-- proof
  apply Finset.prod_pos
  intro ℓ hℓ
  exact Nat.pos_of_ne_zero (pow_ne_zero _ (Finset.mem_filter.mp hℓ).2.ne_zero)

/--
[ecmSmoothScalar_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmSmoothScalar_smooth
  {B M : ℕ} :
-- imply
  ecmSmoothScalar B M ∈ Nat.smoothNumbers B := by
-- proof
  rw [Nat.mem_smoothNumbers]
  constructor
  · exact (ecmSmoothScalar_pos B M).ne'
  · intro q hq
    rw [Nat.mem_primeFactorsList (ecmSmoothScalar_pos B M).ne'] at hq
    obtain ⟨hqp, hq_dvd⟩ := hq
    simp only [ecmSmoothScalar] at hq_dvd
    rw [hqp.prime.dvd_finset_prod_iff (fun ℓ => ℓ ^ ecmSmoothExponent ℓ M)] at hq_dvd
    obtain ⟨ℓ, hℓ_mem, hq_dvd_pow⟩ := hq_dvd
    rw [Finset.mem_filter, Finset.mem_range] at hℓ_mem
    have hq_dvd_ℓ := hqp.dvd_of_dvd_pow hq_dvd_pow
    have hqℓ := (Nat.prime_dvd_prime_iff_eq hqp hℓ_mem.2).mp hq_dvd_ℓ
    omega

/--
[ecmPartialScalar_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecmPartialScalar_smooth
  {ℓ₁ M : ℕ} :
-- imply
  ecmPartialScalar ℓ₁ M ∈ Nat.smoothNumbers (ℓ₁ + 1) := by
-- proof
  rw [Nat.mem_smoothNumbers]
  constructor
  · exact (ecmPartialScalar_pos ℓ₁ M).ne'
  · intro q hq
    rw [Nat.mem_primeFactorsList (ecmPartialScalar_pos ℓ₁ M).ne'] at hq
    obtain ⟨hqp, hq_dvd⟩ := hq
    simp only [ecmPartialScalar] at hq_dvd
    rw [hqp.prime.dvd_finset_prod_iff (fun ℓ => ℓ ^ ecmSmoothExponent ℓ M)] at hq_dvd
    obtain ⟨ℓ, hℓ_mem, hq_dvd_pow⟩ := hq_dvd
    rw [Finset.mem_filter, Finset.mem_range] at hℓ_mem
    have hq_dvd_ℓ := hqp.dvd_of_dvd_pow hq_dvd_pow
    have hqℓ := (Nat.prime_dvd_prime_iff_eq hqp hℓ_mem.2).mp hq_dvd_ℓ
    omega

/--
[Nat.factorization_le_log_of_pos'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma Nat.factorization_le_log_of_pos'
  {n p : ℕ}
-- given
  (hn : 0 < n)
  (hp : 1 < p) :
-- imply
  n.factorization p ≤ Nat.log p n :=
-- proof
  Nat.le_log_of_pow_le hp (le_of_dvd hn (Nat.ordProj_dvd n p))

/--
[prime_pow_dvd_ecmSmoothScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma prime_pow_dvd_ecmSmoothScalar
  {B M p : ℕ}
-- given
  (hp : Nat.Prime p)
  (hpB : p < B) :
-- imply
  p ^ ecmSmoothExponent p M ∣ ecmSmoothScalar B M :=
-- proof
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpB, hp⟩)

/--
[prime_pow_dvd_ecmPartialScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma prime_pow_dvd_ecmPartialScalar
  {ℓ₁ M p : ℕ}
-- given
  (hp : Nat.Prime p)
  (hpB : p ≤ ℓ₁) :
-- imply
  p ^ ecmSmoothExponent p M ∣ ecmPartialScalar ℓ₁ M :=
-- proof
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩)

/--
[smooth_dvd_ecmSmoothScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma smooth_dvd_ecmSmoothScalar
  {n B M : ℕ}
-- given
  (hn : n ≠ 0)
  (hsmooth : n ∈ Nat.smoothNumbers B)
  (hbound : n ≤ (Nat.sqrt M + 1) ^ 2) :
-- imply
  n ∣ ecmSmoothScalar B M := by
-- proof
  rw [Nat.mem_smoothNumbers] at hsmooth
  rw [← Nat.factorization_le_iff_dvd hn (ecmSmoothScalar_pos B M).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hfp : n.factorization p = 0
    · simp [hfp]
    · have hpn : p ∈ n.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hn]
      exact ⟨hp, (hp.dvd_iff_one_le_factorization hn).mpr (Nat.pos_of_ne_zero hfp)⟩
      have hpB : p < B := hsmooth.2 p hpn
      have hdvd := prime_pow_dvd_ecmSmoothScalar (M := M) hp hpB
      have hfact := (hp.pow_dvd_iff_le_factorization (ecmSmoothScalar_pos B M).ne').mp hdvd
      calc n.factorization p
        ≤ Nat.log p n :=
          Nat.factorization_le_log_of_pos' (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmSmoothScalar B M).factorization p := by
          simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

/--
[smooth_dvd_ecmPartialScalar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma smooth_dvd_ecmPartialScalar
  {n ℓ₁ M : ℕ}
-- given
  (hn : n ≠ 0)
  (hsmooth : n ∈ Nat.smoothNumbers (ℓ₁ + 1))
  (hbound : n ≤ (Nat.sqrt M + 1) ^ 2) :
-- imply
  n ∣ ecmPartialScalar ℓ₁ M := by
-- proof
  rw [Nat.mem_smoothNumbers] at hsmooth
  rw [← Nat.factorization_le_iff_dvd hn (ecmPartialScalar_pos ℓ₁ M).ne']
  intro p
  by_cases hp : Nat.Prime p
  · by_cases hfp : n.factorization p = 0
    · simp [hfp]
    · have hpn : p ∈ n.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hn]
      exact ⟨hp, (hp.dvd_iff_one_le_factorization hn).mpr (Nat.pos_of_ne_zero hfp)⟩
      have hpB : p < ℓ₁ + 1 := hsmooth.2 p hpn
      have hpℓ₁ : p ≤ ℓ₁ := by omega
      have hdvd := prime_pow_dvd_ecmPartialScalar (ℓ₁ := ℓ₁) (M := M) hp hpℓ₁
      have hfact := (hp.pow_dvd_iff_le_factorization (ecmPartialScalar_pos ℓ₁ M).ne').mp hdvd
      calc n.factorization p
        ≤ Nat.log p n :=
          Nat.factorization_le_log_of_pos' (Nat.pos_of_ne_zero hn) hp.one_lt
        _ ≤ Nat.log p ((Nat.sqrt M + 1) ^ 2) := Nat.log_mono_right hbound
        _ ≤ (ecmPartialScalar ℓ₁ M).factorization p := by
          simp only [ecmSmoothExponent] at hfact; omega
  · simp [hp]

/--
[ecm_correctness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
lemma ecm_correctness
  {cfg : ECMConfig}
  {params : ECMCurveParams}
  {p₁ p₂ : ℕ}
  [Fact (Nat.Prime p₁)]
  [Fact (Nat.Prime p₂)]
  {ℓ₁ : ℕ}
  {P₁ : (params.curveModP p₁).Point}
  {P₂ : (params.curveModP p₂).Point}
-- given
  (_hne : p₁ ≠ p₂)
  (_hdvd₁ : p₁ ∣ cfg.N)
  (_hdvd₂ : p₂ ∣ cfg.N)
  (hp₁M : p₁ ≤ cfg.M)
  (_hdisc : ¬ (↑cfg.N : ℤ) ∣ params.disc)
  (_hℓ₁_prime : Nat.Prime ℓ₁)
  (_hℓ₁_bound : ℓ₁ < cfg.B)
  (hsmooth₁ : addOrderOf P₁ ∈ Nat.smoothNumbers (ℓ₁ + 1))
  (hord₁_bound : addOrderOf P₁ ≤ (Nat.sqrt p₁ + 1) ^ 2)
  (hnotsmooth₂ : addOrderOf P₂ ∉ Nat.smoothNumbers (ℓ₁ + 1)) :
-- imply
  (ecmPartialScalar ℓ₁ cfg.M) • P₁ = 0 ∧ (ecmPartialScalar ℓ₁ cfg.M) • P₂ ≠ 0 := by
-- proof
  constructor
  ·
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    have hord₁_pos : addOrderOf P₁ ≠ 0 :=
      (Nat.mem_smoothNumbers.mp hsmooth₁).1
    apply smooth_dvd_ecmPartialScalar hord₁_pos hsmooth₁
    calc addOrderOf P₁
      ≤ (Nat.sqrt p₁ + 1) ^ 2 := hord₁_bound
      _ ≤ (Nat.sqrt cfg.M + 1) ^ 2 := by
        apply Nat.pow_le_pow_left
        exact Nat.add_le_add_right (Nat.sqrt_le_sqrt hp₁M) 1
  ·
    intro h
    apply hnotsmooth₂
    exact Nat.mem_smoothNumbers_of_dvd (ecmPartialScalar_smooth ℓ₁ cfg.M)
      (addOrderOf_dvd_of_nsmul_eq_zero h)

/--
[shortWeierstrass_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean)
-/
@[path]
private lemma shortWeierstrass__eq
  [CommRing R]
  {a b : R} :
-- imply
  (shortWeierstrass a b).Δ = -16 * ecmDiscriminant a b := by
-- proof
  apply shortWeierstrass_ a b


-- created on 2026-10-23
