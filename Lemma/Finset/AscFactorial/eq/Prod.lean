import sympy.functions.combinatorial.factorials
import sympy.Basic


/--
Rising factorial \(x^{\overline{k}} = x(x+1)\cdots(x+k-1)\).
[Mathematica](https://mathworld.wolfram.com/RisingFactorial.html)
[SymPy](https://docs.sympy.org/latest/modules/functions/combinatorial.html#sympy.functions.combinatorial.factorials.RisingFactorial)
-/
@[main]
private lemma main
  [CommSemiring α]
-- given
  (x : α)
  (k : ℕ) :
-- imply
  ascFactorial x k = ∏ i : Fin k, (x + i) := by
-- proof
  induction k with
  | zero =>
    simp [ascFactorial]
  | succ k ih =>
    rw [ascFactorial, ascPochhammer_succ_eval, ← ascFactorial, ih]
    rw [Fin.prod_univ_castSucc]
    simp


-- created on 2021-09-20
-- updated on 2026-09-06
