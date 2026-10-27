import Mathlib
import Initialize.Tactic.Attr.Basic
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
open ValuationSubring
open scoped Pointwise


/-- ported from external source -/

private lemma tameCharacter_of_mem
  (P : ValuationSubring (AlgebraicClosure ℚ))
  (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (h : σ π / π ∈ P) : P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dite_eq_left h

private lemma tameCharacter_sub_one_eq_natCast
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {ζ : AlgebraicClosure ℚ} (hζP : ζ ∈ P)
  (hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1) (hζ1 : ζ ≠ 1)
  {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {a : ℕ} (hσζ : σ ζ = ζ ^ a) :
  P.tameCharacter (ζ - 1) σ = a := by
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hq : σ (ζ - 1) / (ζ - 1) = ∑ i ∈ Finset.range a, ζ ^ i := by
    rw [map_sub, map_one, hσζ, div_eq_iff hne, geom_sum_mul]
  have hmem : σ (ζ - 1) / (ζ - 1) ∈ P := by
    rw [hq]
    exact sum_mem fun i _ => pow_mem hζP i
  rw [tameCharacter_of_mem P _ _ hmem]
  have hsum : (⟨σ (ζ - 1) / (ζ - 1), hmem⟩ : P) = ∑ i ∈ Finset.range a, (⟨ζ, hζP⟩ : P) ^ i :=
    Subtype.ext (by
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [SubmonoidClass.coe_pow]
      exact hq)
  rw [hsum, map_sum]
  simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
@[path]
private lemma main
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {ζ : AlgebraicClosure ℚ}
  {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
  {a : ℕ}
-- given
  (hζP : ζ ∈ P)
  (hres : IsLocalRing.residue P ⟨ζ, hζP⟩ = 1)
  (hζ1 : ζ ≠ 1)
  (hσζ : σ ζ = ζ ^ a) :
-- imply
  P.tameCharacter (ζ - 1) σ = a :=
-- proof
  tameCharacter_sub_one_eq_natCast P hζP hres hζ1 hσζ


-- created on 2026-10-23
