import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y : ℝ}
-- given
  (h : x > y ∨ x < y) :
-- imply
  x ≠ y := by
-- proof
  rcases h with h | h
  · exact ne_of_gt h
  · exact ne_of_lt h


@[path]
private lemma main
  {x : α}
  {A B : Set α}
  [DecidablePred (· ∈ A)]
  [DecidablePred (· ∈ B)]
  {f g h : α → β}
  {p : β}
-- given
  (hc : f x ≠ p ∧ x ∈ A ∨ p ≠ g x ∧ x ∈ B \ A ∨ p ≠ h x ∧ x ∉ A ∪ B) :
-- imply
  (if x ∈ A then f x else if x ∈ B \ A then g x else h x) ≠ p := by
-- proof
  rcases hc with ⟨h₁, ha⟩ | hc
  · rw [if_pos ha]
    exact h₁
  · rcases hc with ⟨h₁, hb⟩ | ⟨h₁, hn⟩
    · rw [if_neg hb.2, if_pos hb]
      exact h₁.symm
    · rw [Set.mem_union, not_or] at hn
      rw [if_neg hn.1, if_neg (fun hh => hn.2 hh.1)]
      exact h₁.symm


@[path]
private lemma two
  {x : α}
  {A : Set α}
  [DecidablePred (· ∈ A)]
  {f g : α → β}
  {p : β}
-- given
  (h : p ≠ f x ∧ x ∈ A ∨ g x ≠ p ∧ x ∉ A) :
-- imply
  p ≠ (if x ∈ A then f x else g x) := by
-- proof
  rcases h with ⟨h₁, ha⟩ | ⟨h₁, hn⟩
  · rw [if_pos ha]
    exact h₁
  · rw [if_neg hn]
    exact h₁.symm


-- created on 2023-04-19
