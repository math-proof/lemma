import Mathlib
import sympy.Basic


/--
[Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_span_le_pow_of_forall_isIdempotentElem_of_subset.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {S : Set R}
  {𝔭 : Ideal R}
  {n : ℕ}
-- given
  (hS : ∀ e ∈ S, IsIdempotentElem e)
  (hS𝔭 : S ⊆ 𝔭) :
-- imply
  Ideal.span S ≤ 𝔭 ^ n := by
-- proof
  rcases n with _ | n
  · rw [pow_zero, Ideal.one_eq_top]; exact le_top
  · rw [Ideal.span_le]
    intro e he
    have h := Ideal.pow_mem_pow (hS𝔭 he) (n + 1)
    rwa [(hS e he).pow_succ_eq] at h


-- created on 2026-10-03
