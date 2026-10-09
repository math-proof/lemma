import sympy.functions.combinatorial.numbers
import sympy.Basic
import Mathlib.Data.Set.Card


@[path]
private lemma main
  {n k : ℕ}
-- given
  (_h : k < n) :
-- imply
  let A : Fin (k + 1) → Set (Finset (Finset ℕ)) := fun j =>
    (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) '' Stirling.conditionset n (k + 1)
  (⋃ j, A j).ncard = ∑ j, (A j).ncard := by
-- proof
  -- sorry: false as stated (unproved in py). Stirling.conditionset holds ordered tuples, so every A j is the same set of partitions; n = 2, k = 1 gives 2 on the lhs vs 4 on the rhs
  sorry


-- created on 2020-08-11
