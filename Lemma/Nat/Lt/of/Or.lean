import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
  {x : α}
  {f g h : α → ℝ}
  {p : ℝ}
-- given
  (hc : f x < p ∧ x ∈ A ∨ g x < p ∧ x ∈ B \ A ∨ h x < p ∧ x ∉ A ∪ B) :
-- imply
  (if x ∈ A then f x else if x ∈ B \ A then g x else h x) < p := by
-- proof
  obtain ⟨h₁, ha⟩ | hc := hc
  ·
    rwa [ite_eq_left ha]
  ·
    obtain ⟨h₁, hb⟩ | ⟨h₁, hn⟩ := hc
    ·
      rwa [ite_eq_right hb.2, ite_eq_left hb]
    ·
      rw [Set.mem_union, not_or] at hn
      rwa [ite_eq_right hn.1, ite_eq_right (fun hh => hn.2 hh.1)]


@[path]
private lemma two
  {A : Set α} [DecidablePred (· ∈ A)]
  {x : α}
  {f g : α → ℝ}
  {p : ℝ}
-- given
  (h : f x < p ∧ x ∈ A ∨ g x < p ∧ x ∉ A) :
-- imply
  (if x ∈ A then f x else g x) < p := by
-- proof
  obtain ⟨h₁, ha⟩ | ⟨h₁, hn⟩ := h
  ·
    rwa [ite_eq_left ha]
  ·
    rwa [ite_eq_right hn]


-- created on 2019-08-06
