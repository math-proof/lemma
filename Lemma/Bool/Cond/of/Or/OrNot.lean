import sympy.Basic


@[main]
private lemma main
-- given
  (h₀ : q ∨ p)
  (h₁ : ¬q ∨ p) :
-- imply
  p := by
-- proof
    -- Use case analysis on the disjunction h₀ : q ∨ p
  cases h₀ with
  | inl hq =>
      -- If q is true, use case analysis on h₁ : ¬q ∨ p
    cases h₁ with
    | inl hnq =>
        -- If ¬q is true, we have a contradiction with hq : q
      contradiction
    | inr hp =>
        -- If p is true, we have the desired conclusion
      exact hp
  | inr hp =>
      -- If p is true, we have the desired conclusion
    exact hp


-- created on 2025-04-07
