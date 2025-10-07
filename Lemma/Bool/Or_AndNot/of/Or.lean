import sympy.Basic


@[main]
private lemma main
-- given
  (h : p ∨ q) :
-- imply
  p ∨ (¬p ∧ q) := by
-- proof
  -- Consider the two cases of the disjunction in the hypothesis
  cases h with
  | inl hnp =>
    -- Case 1: ¬p is true
    -- The conclusion ¬p ∨ (p ∧ q) is true because ¬p is true
    exact Or.inl hnp
  | inr hq =>
    -- Case 2: q is true
    -- Now, check the truth value of p
    by_cases hp : p
    -- Subcase 2.1: p is true
    -- Since p and q are both true, p ∧ q is true, making the conclusion true
    simp_all
    -- Subcase 2.2: p is false
    -- Since ¬p is true, the conclusion is true
    simp_all


-- created on 2025-04-07
