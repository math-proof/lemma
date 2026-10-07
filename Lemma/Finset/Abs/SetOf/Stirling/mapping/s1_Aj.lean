import sympy.functions.combinatorial.numbers
import sympy.Basic


@[main]
private lemma main
  {n k : ℕ}
  {j : Fin (k + 1)} :
-- imply
  ((fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n (k + 1)).ncard =
    ((fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) '' Stirling.conditionset n (k + 1)).ncard := by
-- proof
  -- sorry: false as stated (unproved in py). `Stirling.conditionset` holds ordered tuples, so `A j` puts `n` into
  -- whichever block the ordering places at `j`: n = 2, k = 1, j = 0 gives lhs 1 ({{0},{1}}) vs rhs 2 ({{0,2},{1}}, {{1,2},{0}})
  sorry


-- created on 2026-10-07
