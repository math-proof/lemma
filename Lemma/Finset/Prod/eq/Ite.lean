import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {C D A B : Finset ℤ}
  {x : ℤ}
  {f h : ℤ → ℤ → ℝ} :
-- imply
  ∑ i ∈ C, ∑ j ∈ D, (if x ∈ A ∪ B then f i j else h i j) =
    if x ∈ A ∪ B then ∑ i ∈ C, ∑ j ∈ D, f i j else ∑ i ∈ C, ∑ j ∈ D, h i j := by
-- proof
  by_cases hx : x ∈ A ∪ B
  · simp only [if_pos hx]
  · simp only [if_neg hx]


-- created on 2020-03-10
