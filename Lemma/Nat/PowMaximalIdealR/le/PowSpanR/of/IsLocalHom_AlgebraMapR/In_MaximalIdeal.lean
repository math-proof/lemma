import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_maximalIdeal_pow_le_span_natCast_pow_of_module_finite.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [CharZero 𝒪] [CommRing R] [IsLocalRing R] [Algebra 𝒪 R] [Module.Finite 𝒪 R]
  {p : ℕ} [Fact p.Prime]
  {n : ℕ}
-- given
  (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
  (hl : IsLocalHom (algebraMap 𝒪 R)) :
-- imply
  ∃ m : ℕ, maximalIdeal R ^ m ≤ Ideal.span {(p : R)} ^ n := by
-- proof
  classical
  set J : Ideal R := Ideal.map (algebraMap 𝒪 R) (maximalIdeal 𝒪) with hJ
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing 𝒪 R

  have h1 : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have hcomap : P.comap (algebraMap 𝒪 R) = maximalIdeal 𝒪 :=
      ((IsLocalRing.maximalIdeal.isMaximal 𝒪).eq_of_le (Ideal.comap_ne_top _ hP.ne_top)
        (Ideal.map_le_iff_le_comap.1 hJP)).symm
    have hmax : (P.comap (algebraMap 𝒪 R)).IsMaximal := hcomap ▸ IsLocalRing.maximalIdeal.isMaximal 𝒪
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hmax
    exact (IsLocalRing.eq_maximalIdeal this).ge
  obtain ⟨a, ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (IsNoetherian.noetherian _)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hp0 : (p : 𝒪) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨e, hpe⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  have hspan : Ideal.span {(p : 𝒪)} = maximalIdeal 𝒪 ^ e := by
    rw [Ideal.span_singleton_eq_span_singleton.2 hpe, ← Ideal.span_singleton_pow, hϖ.maximalIdeal_eq]

  refine ⟨a * (e * n), ?_⟩
  calc maximalIdeal R ^ (a * (e * n)) = (maximalIdeal R ^ a) ^ (e * n) := pow_mul _ _ _
    _ ≤ J ^ (e * n) := Ideal.pow_right_mono ha _
    _ = Ideal.span {(p : R)} ^ n := by
      rw [hJ, ← Ideal.map_pow, pow_mul, ← hspan, Ideal.span_singleton_pow, Ideal.map_span,
        Set.image_singleton, map_pow, map_natCast, ← Ideal.span_singleton_pow]


-- created on 2026-10-05
