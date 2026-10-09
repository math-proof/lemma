import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Set α}
  {f : ℕ → Set α} :
-- imply
  (⋂ k ∈ Finset.range n, f k) ∪ x = ⋂ k ∈ Finset.range n, (f k ∪ x) := by
-- proof
  ext y
  simp only [Set.mem_union, Set.mem_iInter]
  constructor
  · intro h
    obtain hy | hy := h
    · exact fun k hk => Or.inl (hy k hk)
    · exact fun _ _ => Or.inr hy
  · intro h
    if hy : y ∈ x then
      exact Or.inr hy
    else
      exact Or.inl fun k hk => (h k hk).resolve_right hy


-- created on 2021-07-11
