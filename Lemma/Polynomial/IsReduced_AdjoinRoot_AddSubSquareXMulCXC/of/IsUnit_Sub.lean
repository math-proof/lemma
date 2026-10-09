import Mathlib
import sympy.Basic

open Polynomial

/--
[AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_isReduced_of_isReduced_of_isUnit_sq_sub_four_mul.lean)
-/

private lemma monic_quad
  {R : Type*}
  [CommRing R]
  (t n : R) : (X ^ 2 - C t * X + C n : R[X]).Monic := by
  nontriviality R
  monicity!

private lemma degree_quad
  {R : Type*}
  [CommRing R]
  [Nontrivial R] (t n : R) : (X ^ 2 - C t * X + C n : R[X]).degree = 2 := by
  compute_degree!

private lemma exists_eq_mk
    {R : Type*}
    [CommRing R]
    (t n : R) (z : AdjoinRoot (X ^ 2 - C t * X + C n : R[X])) :
    ∃ a b : R, z = AdjoinRoot.mk _ (C b * X + C a) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton (AdjoinRoot (X ^ 2 - C t * X + C n : R[X])) :=
      (AdjoinRoot.of _).codomain_trivial
    exact ⟨0, 0, Subsingleton.elim _ _⟩
  · obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective z
    set f : R[X] := X ^ 2 - C t * X + C n with hf
    have hmonic : f.Monic := monic_quad t n
    refine ⟨(g %ₘ f).coeff 0, (g %ₘ f).coeff 1, ?_⟩
    have hdeg : (g %ₘ f).degree ≤ 1 := by
      have h := degree_modByMonic_lt g hmonic
      rw [degree_quad] at h
      exact Order.le_of_lt_succ h
    rw [← eq_X_add_C_of_degree_le_one hdeg, AdjoinRoot.mk_eq_mk]
    refine ⟨g /ₘ f, ?_⟩
    have := modByMonic_add_div g f
    rw [hf] at this ⊢
    linear_combination -this

private lemma isCoprime_quad_of_isUnit
    {R : Type*}
    [CommRing R]
    (t n : R) (h : IsUnit (t ^ 2 - 4 * n)) :
    IsCoprime (X ^ 2 - C t * X + C n : R[X]) (derivative (X ^ 2 - C t * X + C n : R[X])) := by
  obtain ⟨d, hd⟩ := h
  have hder : derivative (X ^ 2 - C t * X + C n : R[X]) = C 2 * X - C t := by
    simp only [derivative_add, derivative_sub, derivative_X_pow, derivative_C_mul_X, derivative_C]
    simp [C_ofNat]
  rw [hder]
  refine ⟨C (-4 * (↑d⁻¹ : R)), C (↑d⁻¹ : R) * (C 2 * X - C t), ?_⟩
  have key : (C 2 * X - C t : R[X]) * (C 2 * X - C t) - 4 * (X ^ 2 - C t * X + C n) =
      C (t ^ 2 - 4 * n) := by
    simp only [map_sub, map_mul, map_pow, C_ofNat]
    ring
  have hdinv : (↑d⁻¹ : R) * (t ^ 2 - 4 * n) = 1 := by rw [← hd, Units.inv_mul]
  calc C (-4 * (↑d⁻¹ : R)) * (X ^ 2 - C t * X + C n) + C (↑d⁻¹ : R) * (C 2 * X - C t) * (C 2 * X - C t)
      = C (↑d⁻¹ : R) * ((C 2 * X - C t) * (C 2 * X - C t) - 4 * (X ^ 2 - C t * X + C n)) := by
        simp only [map_mul, map_neg, C_ofNat]; ring
    _ = C ((↑d⁻¹ : R) * (t ^ 2 - 4 * n)) := by rw [key, ← map_mul]
    _ = 1 := by rw [hdinv, map_one]

private lemma isReduced_field
    {F : Type*} [Field F] (t n : F) (h : IsUnit (t ^ 2 - 4 * n)) :
    IsReduced (AdjoinRoot (X ^ 2 - C t * X + C n : F[X])) := by
  have hsep : (X ^ 2 - C t * X + C n : F[X]).Separable := isCoprime_quad_of_isUnit t n h
  exact (Ideal.isRadical_iff_quotient_reduced _).1
    (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)

private lemma isReduced_of_isReduced
    {R : Type*}
    [CommRing R]
    [IsReduced R] (t n : R) (h : IsUnit (t ^ 2 - 4 * n)) :
    IsReduced (AdjoinRoot (X ^ 2 - C t * X + C n : R[X])) := by
  refine ⟨fun z hz => ?_⟩
  obtain ⟨a, b, rfl⟩ := exists_eq_mk t n z

  have hab : ∀ q : Ideal R, q.IsPrime → a ∈ q ∧ b ∈ q := by
    intro q hq
    let Fq := q.ResidueField
    let π : R →+* Fq := algebraMap R Fq
    set fq : Fq[X] := X ^ 2 - C (π t) * X + C (π n) with hfq
    have hmap : (X ^ 2 - C t * X + C n : R[X]).map π = fq := by
      simp [hfq, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

    let φ : AdjoinRoot (X ^ 2 - C t * X + C n : R[X]) →+* AdjoinRoot fq :=
      AdjoinRoot.lift ((AdjoinRoot.of fq).comp π) (AdjoinRoot.root fq) (by
        rw [← Polynomial.eval₂_map, hmap]
        exact AdjoinRoot.eval₂_root fq)
    have hφ : φ (AdjoinRoot.mk _ (C b * X + C a)) = AdjoinRoot.mk fq (C (π b) * X + C (π a)) := by
      change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk _ _) = _
      rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
      congr 1
      simp [Polynomial.map_add, Polynomial.map_mul]
    have hunit : IsUnit (π t ^ 2 - 4 * π n) := by
      have h4 : π (t ^ 2 - 4 * n) = π t ^ 2 - 4 * π n := by
        rw [map_sub, map_pow, map_mul, map_ofNat]
      exact h4 ▸ h.map π
    have := isReduced_field (π t) (π n) hunit
    have hz' : IsNilpotent (φ (AdjoinRoot.mk _ (C b * X + C a))) := hz.map φ
    have h0 := hz'.eq_zero
    rw [hφ, AdjoinRoot.mk_eq_zero] at h0

    have hzero : (C (π b) * X + C (π a) : Fq[X]) = 0 := by
      refine Polynomial.eq_zero_of_dvd_of_degree_lt h0 ?_
      rw [hfq, degree_quad]
      exact lt_of_le_of_lt (degree_linear_le) (by decide)
    have hb : π b = 0 := by
      have := congrArg (fun p : Fq[X] => p.coeff 1) hzero
      simpa using this
    have ha : π a = 0 := by
      have := congrArg (fun p : Fq[X] => p.coeff 0) hzero
      simpa using this
    exact ⟨(Ideal.algebraMap_residueField_eq_zero).1 ha, (Ideal.algebraMap_residueField_eq_zero).1 hb⟩
  have ha : IsNilpotent a := by
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    exact fun q hq => (hab q hq).1
  have hb : IsNilpotent b := by
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    exact fun q hq => (hab q hq).2
  rw [ha.eq_zero, hb.eq_zero]
  simp
@[path]
private lemma main
  [CommRing R] [IsReduced R]
  {t n : R}
-- given
  (h : IsUnit (t ^ 2 - 4 * n)) :
-- imply
  IsReduced (AdjoinRoot (X ^ 2 - C t * X + C n : R[X])) :=
-- proof
  isReduced_of_isReduced t n h


-- created on 2026-10-09
