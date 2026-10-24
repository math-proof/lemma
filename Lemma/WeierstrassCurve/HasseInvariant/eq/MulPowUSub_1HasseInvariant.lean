import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_Polynomial_DeuringPolynomial
import Lemma.Definitions.Def_WeierstrassCurve_HasseInvariant
import Lemma.Int.P2MUtil
open Polynomial
open WeierstrassCurve Int


/-- ported from external source -/
@[path]
private lemma main
  [CommRing R]
  {q : ℕ} [Fact q.Prime] [CharP R q]
  {W : WeierstrassCurve R}
  {v : VariableChange R} :
-- imply
  (v • W).hasseInvariant q = ((v.u⁻¹ : Rˣ) : R) ^ (q - 1) * W.hasseInvariant q := by
-- proof
  have natCast_choose_prime_sub_one_eq_zero {k : ℕ} (h1 : q - 1 < k) (h2 : k ≤ 2 * q - 2) :
      ((k.choose (q - 1) : ℕ) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R q]
    have hq := ‹Fact q.Prime›.out.one_lt
    exact ‹Fact q.Prime›.out.dvd_choose (by omega) (by omega) (by omega)
  have coeff_comp_C_mul_X_sub_C_of_charP (P : R[X]) (hP : P.natDegree ≤ 2 * q - 2) (a r : R) :
      (P.comp (C a * (X - C r))).coeff (q - 1) = a ^ (q - 1) * P.coeff (q - 1) := by
    have hq := ‹Fact q.Prime›.out.one_lt
    conv_lhs => rw [P.as_sum_range' (2 * q - 1) (by omega), sum_comp, finsetSum_coeff]
    have hterm : ∀ i, ((monomial i (P.coeff i)).comp (C a * (X - C r))).coeff (q - 1) =
        P.coeff i * (a ^ i * ((-r) ^ (i - (q - 1)) * (i.choose (q - 1) : R))) := by
      intro i
      rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, coeff_C_mul,
        coeff_C_mul, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
    simp_rw [hterm]
    rw [Finset.sum_eq_single (q - 1)]
    ·
      simp
      ring
    ·
      intro i _ hi
      obtain hlt | hgt := lt_or_gt_of_ne hi
      ·
        rw [Nat.choose_eq_zero_of_lt hlt]
        simp
      ·
        by_cases hi2 : i ≤ 2 * q - 2
        ·
          rw [natCast_choose_prime_sub_one_eq_zero hgt hi2]
          simp
        ·
          have : P.coeff i = 0 := P.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [this]; simp
    ·
      intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  have twoTorsionPolynomial_variableChange_comp :
      ((v • W).twoTorsionPolynomial.toPoly).comp (C ((v.u⁻¹ : Rˣ) : R) ^ 2 * (X - C v.r)) =
        C (((v.u⁻¹ : Rˣ) : R) ^ 6) * W.twoTorsionPolynomial.toPoly := by
    simp only [twoTorsionPolynomial, Cubic.toPoly, variableChange_b₂, variableChange_b₄,
      variableChange_b₆, add_comp, mul_comp, pow_comp, X_comp, C_comp, ofNat_comp,
      map_mul, map_add, map_pow, map_ofNat]
    ring
  obtain h2 | hodd := ‹Fact q.Prime›.out.eq_two_or_odd'
  ·
    subst h2
    simp [hasseInvariant, coeff_one]
  obtain ⟨m, hm⟩ := hodd
  have hm1 : (q - 1) / 2 = m := by omega
  have hm2 : q - 1 = 2 * m := by omega
  set ui : R := ((v.u⁻¹ : Rˣ) : R) with hui
  have key := congrArg (fun P => (P ^ m).coeff (q - 1)) twoTorsionPolynomial_variableChange_comp
  have hdeg : ((v • W).twoTorsionPolynomial.toPoly ^ m).natDegree ≤ 2 * q - 2 := by
    refine natDegree_pow_le.trans ?_
    have h3 : (v • W).twoTorsionPolynomial.toPoly.natDegree ≤ 3 := natDegree_cubic_le
    calc
      _ ≤ m * 3 := Nat.mul_le_mul_left m h3
      _ ≤ 2 * q - 2 := by omega
  rw [← pow_comp, ← C_pow, coeff_comp_C_mul_X_sub_C_of_charP _ hdeg, mul_pow, ← C_pow, coeff_C_mul] at key
  rw [hasseInvariant, hasseInvariant, hm1]
  have key' :
      (((v.u⁻¹ ^ (4 * m) : Rˣ)) : R) * ((v • W).twoTorsionPolynomial.toPoly ^ m).coeff (q - 1) =
        (((v.u⁻¹ ^ (4 * m) : Rˣ)) : R) *
          (ui ^ (q - 1) * (W.twoTorsionPolynomial.toPoly ^ m).coeff (q - 1)) := by
    rw [Units.val_pow_eq_pow_val, ← hui, hm2]
    rw [hm2] at key
    calc
      _ = (ui ^ 2) ^ (2 * m) * ((v • W).twoTorsionPolynomial.toPoly ^ m).coeff (2 * m) := by ring
      _ = (ui ^ 6) ^ m * (W.twoTorsionPolynomial.toPoly ^ m).coeff (2 * m) := key
      _ = ui ^ (4 * m) * (ui ^ (2 * m) * (W.twoTorsionPolynomial.toPoly ^ m).coeff (2 * m)) := by
        ring
  exact (Units.mul_right_inj _).mp key'


-- created on 2026-10-24
