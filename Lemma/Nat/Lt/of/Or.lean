import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
  [DecidablePred (· ∈ A)]
  [DecidablePred (· ∈ B)]
  {f g h : α → ℝ}
  {p : ℝ}
-- given
  (hc : f x < p ∧ x ∈ A ∨ g x < p ∧ x ∈ B \ A ∨ h x < p ∧ x ∉ A ∪ B) :
-- imply
  (if x ∈ A then f x else if x ∈ B \ A then g x else h x) < p := by
-- proof
  rcases hc with ⟨h₁, ha⟩ | hc
  · rw [if_pos ha]
    exact h₁
  · rcases hc with ⟨h₁, hb⟩ | ⟨h₁, hn⟩
    · rw [if_neg hb.2, if_pos hb]
      exact h₁
    · rw [Set.mem_union, not_or] at hn
      rw [if_neg hn.1, if_neg (fun hh => hn.2 hh.1)]
      exact h₁


@[main]
private lemma two
  {x : α}
  {A : Set α}
  [DecidablePred (· ∈ A)]
  {f g : α → ℝ}
  {p : ℝ}
-- given
  (h : f x < p ∧ x ∈ A ∨ g x < p ∧ x ∉ A) :
-- imply
  (if x ∈ A then f x else g x) < p := by
-- proof
  rcases h with ⟨h₁, ha⟩ | ⟨h₁, hn⟩
  · rw [if_pos ha]
    exact h₁
  · rw [if_neg hn]
    exact h₁


-- created on 2026-09-27
