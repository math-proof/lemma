import Mathlib
import sympy.Basic
import Def.FLTPrelim_Ramification
import Def.GaloisRep_TameCharacter


/-- ported from external source -/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {P : ValuationSubring (AlgebraicClosure ℚ)}
  {π : AlgebraicClosure ℚ}
-- given
  (hP : P.LiesOverPrime p)
  (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (hσ : σ ∈ P.inertiaSubgroupIn ℚ) :
-- imply
  P.tameCharacter π σ ^ (p ^ 2 - 1) = 1 := by
  classical
    have hp : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hn : p ^ 2 - 1 ≠ 0 := by
-- proof
      have : 2 ≤ p := (Fact.out : p.Prime).two_le
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    have hπ0 : π ≠ 0 := by
      intro h; rw [h, zero_pow hn] at hπ; exact hp hπ.symm
    set u : AlgebraicClosure ℚ := σ π / π with hu
    have hun : u ^ (p ^ 2 - 1) = 1 := by
      rw [hu, div_pow, ← map_pow, hπ, map_natCast, div_self hp]
    have huP : u ∈ P := by
      rw [← P.valuation_le_one_iff]
      have hv : P.valuation u ^ (p ^ 2 - 1) = 1 := by rw [← map_pow, hun, map_one]
      refine ((pow_eq_one_iff.1 hv).resolve_right hn).le
    unfold ValuationSubring.tameCharacter
    rw [dite_eq_left huP, ← map_pow]
    have : (⟨u, huP⟩ : P) ^ (p ^ 2 - 1) = 1 := Subtype.ext (by simpa using hun)
    rw [this, map_one]


-- created on 2026-10-23
