import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A : Finset ι}
  {f g : ι → ℝ} :
-- imply
  ∑ x ∈ A, (if g x > 0 then f x else 0) = ∑ x ∈ A.filter (fun x => g x > 0), f x := by
-- proof
  exact (Finset.sum_filter _ _).symm


-- created on 2020-03-14
