import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GaloisRep_TameCharacter
import Def.FLTPrelim_Ramification
import Lemma.EllipticCurve.FrobeniusTrace
import Lemma.Int.P2MUtil

open ValuationSubring
open scoped Pointwise

/--
[ValuationSubring_tameCharacter_pow_left](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_tameCharacter_pow_left.lean)
-/

private theorem tameCharacter_of_mem
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∈ P) : P.tameCharacter π σ = IsLocalRing.residue P ⟨σ π / π, h⟩ := by
  unfold ValuationSubring.tameCharacter
  exact dif_pos h

private theorem tameCharacter_of_not_mem
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (h : σ π / π ∉ P) : P.tameCharacter π σ = 0 := by
  unfold ValuationSubring.tameCharacter
  exact dif_neg h

private theorem tameCharacter_pow_left_of_mem
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσπ : σ π / π ∈ P) (m : ℕ) :
    P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m := by
  have hq : σ (π ^ m) / π ^ m = (σ π / π) ^ m := by rw [map_pow, div_pow]
  have hmem : σ (π ^ m) / π ^ m ∈ P := by
    rw [hq]
    exact pow_mem hσπ m
  rw [tameCharacter_of_mem P _ _ hmem, tameCharacter_of_mem P _ _ hσπ, ← map_pow]
  congr 1
  exact Subtype.ext (by simp only [SubmonoidClass.coe_pow]; exact hq)

private theorem pow_not_mem
  (P : ValuationSubring (AlgebraicClosure ℚ))
  {u : AlgebraicClosure ℚ} (hu : u ∉ P) {m : ℕ} (hm : 0 < m) : u ^ m ∉ P := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (ValuationSubring.zero_mem P)
  have hinv : u⁻¹ ∈ P := (P.mem_or_inv_mem u).resolve_left hu
  have hmax : (⟨u⁻¹, hinv⟩ : P) ∈ IsLocalRing.maximalIdeal P :=
    coe_mem_nonunits_iff.mp ((mem_nonunits_iff_or P).mpr (Or.inr (by rwa [inv_inv])))
  have hpow : (⟨u⁻¹, hinv⟩ : P) ^ m ∈ IsLocalRing.maximalIdeal P :=
    Ideal.pow_mem_of_mem _ hmax m hm
  have hnu : ((⟨u⁻¹, hinv⟩ : P) ^ m : P).1 ∈ P.nonunits := coe_mem_nonunits_iff.mpr hpow
  rw [SubmonoidClass.coe_pow] at hnu
  change (u⁻¹) ^ m ∈ P.nonunits at hnu
  rcases (mem_nonunits_iff_or P).mp hnu with h | h
  · exact absurd h (pow_ne_zero m (inv_ne_zero hu0))
  · rwa [inv_pow, inv_inv] at h

private theorem tameCharacter_pow_left
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (π : AlgebraicClosure ℚ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : ℕ) : P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m := by
  by_cases hσπ : σ π / π ∈ P
  · exact tameCharacter_pow_left_of_mem P π hσπ m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h1 : σ (π ^ 0) / π ^ 0 ∈ P := by
      rw [pow_zero, map_one, div_one]
      exact ValuationSubring.one_mem P
    rw [tameCharacter_of_mem P _ _ h1, pow_zero (P.tameCharacter π σ), ← map_one (IsLocalRing.residue P)]
    congr 1
    exact Subtype.ext (by change σ (π ^ 0) / π ^ 0 = 1; rw [pow_zero, map_one, div_one])
  · have hq : σ (π ^ m) / π ^ m = (σ π / π) ^ m := by rw [map_pow, div_pow]
    have hnot : σ (π ^ m) / π ^ m ∉ P := by
      rw [hq]
      exact pow_not_mem P hσπ hm
    rw [tameCharacter_of_not_mem P _ _ hnot, tameCharacter_of_not_mem P _ _ hσπ, zero_pow hm.ne']
@[path]
private lemma main
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {π : AlgebraicClosure ℚ}
  {m : ℕ}
-- given
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
-- imply
  P.tameCharacter (π ^ m) σ = P.tameCharacter π σ ^ m :=
-- proof
  tameCharacter_pow_left P π σ m


-- created on 2026-10-23
