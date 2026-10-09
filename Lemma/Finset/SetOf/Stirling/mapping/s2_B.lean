import sympy.functions.combinatorial.numbers
import sympy.Basic


@[path]
private lemma main
  {n k : ℕ} :
-- imply
  {e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) | ({n} : Finset ℕ) ∈ e} =
    (fun e => insert {n} e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k) := by
-- proof
  sorry


-- created on 2020-09-29
