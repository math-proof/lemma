import sympy.Basic
open Nat


@[path]
private lemma main
  {n : ℕ} :
-- imply
  ∏ i ∈ Finset.range n, (n - i) = n ! := by
-- proof
  rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun j => j + 1) n]
  refine Finset.prod_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  omega


-- created on 2022-01-15
