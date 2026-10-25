import Mathlib
import sympy.Basic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil


/--
[ValuationSubring_exists_liesOverPrime_algebraicClosure_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat.lean)
-/
@[path]
private lemma main
  {p : Nat.Primes} :
-- imply
  ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by
-- proof
  have hq : (p : ℕ).Prime := p.2

  set R : Subring (AlgebraicClosure ℚ) := ⊥ with hR

  have hqR : ¬IsUnit (((p : ℕ) : ℕ) : R) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨y, hy⟩
    have hy' : ((p : ℕ) : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (R.subtype) hy
      simpa using this
    obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
    rw [← hn] at hy'
    have hqn : ((p : ℕ) : ℤ) * n = 1 := by
      have : ((((p : ℕ) : ℤ) * n : ℤ) : AlgebraicClosure ℚ) = ((1 : ℤ) : AlgebraicClosure ℚ) := by
        push_cast
        linear_combination hy'
      exact_mod_cast this
    have h1 : ((p : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨n, hqn.symm⟩
    have h2 : 2 ≤ (p : ℕ) := hq.two_le
    omega

  obtain ⟨B, -, hB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (Ideal.span {(((p : ℕ) : ℕ) : R)})
      (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  refine ⟨B, hB ⟨(((p : ℕ) : ℕ) : R), Ideal.subset_span rfl, ?_⟩⟩
  simp


-- created on 2026-10-23
