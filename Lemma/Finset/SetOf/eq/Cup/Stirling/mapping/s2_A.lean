import sympy.functions.combinatorial.numbers
import sympy.Basic
import Lemma.Finset.SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J
open Finset


@[path]
private lemma main
  {n k : ℕ} :
-- imply
  {e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) | ({n} : Finset ℕ) ∉ e} =
    ⋃ j : Fin (k + 1), (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) '' Stirling.conditionset n (k + 1) :=
-- proof
  SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J


-- created on 2020-10-03
