import Mathlib
import sympy.Basic


/--
[Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_forall_not_countable_setOf_re_gt_mem_of_finite.lean)
-/
@[main]
private lemma main
  [Finite ι]
  {S : ι → Set ℂ}
-- given
  (h : ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ ∃ i, s ∈ S i}) :
-- imply
  ∃ i, ∀ σ' : ℝ, ¬ Set.Countable {s : ℂ | σ' < s.re ∧ s ∈ S i} := by
-- proof
  classical
  by_contra hcon
  push Not at hcon

  choose σ hσ using hcon

  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i, σ i ≤ M := by
    obtain ⟨M, hM⟩ := (Set.range σ).toFinite.bddAbove
    exact ⟨M, fun i => hM (Set.mem_range_self i)⟩
  haveI : Countable ι := Finite.to_countable
  apply h M
  have hsub : {s : ℂ | M < s.re ∧ ∃ i, s ∈ S i} ⊆ ⋃ i, {s : ℂ | σ i < s.re ∧ s ∈ S i} := by
    rintro s ⟨hs, i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, lt_of_le_of_lt (hM i) hs, hi⟩
  exact (Set.countable_iUnion fun i => hσ i).mono hsub


-- created on 2026-10-05
