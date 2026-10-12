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
  obtain h | h := h
  · exact ne_of_gt h
  · exact ne_of_lt h


@[path]
private lemma main
  {A B : Set α} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
  {x : α}
  {f g h : α → β}
  {p : β}
-- given
  (hc : f x ≠ p ∧ x ∈ A ∨ p ≠ g x ∧ x ∈ B \ A ∨ p ≠ h x ∧ x ∉ A ∪ B) :
-- imply
  (if x ∈ A then f x else if x ∈ B \ A then g x else h x) ≠ p := by
-- proof
  obtain ⟨h₁, ha⟩ | hc := hc
  ·
    rwa [ite_eq_left ha]
  ·
    obtain ⟨h₁, hb⟩ | ⟨h₁, hn⟩ := hc
    ·
      apply Ne.symm
      rwa [ite_eq_right hb.2, ite_eq_left hb]
    ·
      rw [Set.mem_union, not_or] at hn
      apply Ne.symm
      rwa [ite_eq_right hn.1, ite_eq_right (fun hh => hn.2 hh.1)]


@[path]
private lemma two
  {A : Set α} [DecidablePred (· ∈ A)]
  {x : α}
  {f g : α → β}
  {p : β}
-- given
  (h : p ≠ f x ∧ x ∈ A ∨ g x ≠ p ∧ x ∉ A) :
-- imply
  p ≠ (if x ∈ A then f x else g x) := by
-- proof
  obtain ⟨h₁, ha⟩ | ⟨h₁, hn⟩ := h
  ·
    rwa [ite_eq_left ha]
  ·
    apply Ne.symm
    rwa [ite_eq_right hn]


-- created on 2023-04-19
