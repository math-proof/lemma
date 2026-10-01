import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
-- given
  (h : x ≥ 0) :
-- imply
  x ≤ fun _ => ∑ j, x j := by
-- proof
  intro i
  exact Finset.single_le_sum (fun j _ => h j) (Finset.mem_univ i)


-- created on 2022-04-01
