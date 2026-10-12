import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {C D A B : Finset ℤ}
  {x : ℤ}
  {f h : ℤ → ℤ → ℝ} :
-- imply
  ∑ i ∈ C, ∑ j ∈ D, (if x ∈ A ∪ B then f i j else h i j) =
    if x ∈ A ∪ B then ∑ i ∈ C, ∑ j ∈ D, f i j else ∑ i ∈ C, ∑ j ∈ D, h i j := by
-- proof
  by_cases hx : x ∈ A ∪ B
  · simp only [ite_eq_left hx]
  · simp only [ite_eq_right hx]


-- created on 2020-03-10
