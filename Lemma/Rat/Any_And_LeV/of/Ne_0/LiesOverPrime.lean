import Mathlib
import sympy.Basic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil


/--
[ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  {ε : A.ValueGroup}
-- given
  (hA : A.LiesOverPrime p)
  (hε : ε ≠ 0) :
-- imply
  ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y ≤ ε := by
-- proof
  obtain ⟨x, hx⟩ := A.valuation_surjective ε
  refine ⟨((WithVal.toVal A.valuation x : WithVal A.valuation) : A.valuation.Completion), ?_, ?_⟩
  · intro h
    apply hε
    have := congrArg (Valued.v (R := A.valuation.Completion)) h
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx, map_zero] at this
    exact this
  · rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx]


-- created on 2026-10-23
