import sympy.functions.combinatorial.factorials
import sympy.Basic


/--
Falling factorial \(x^{\underline{k}} = x(x-1)\cdots(x-k+1)\).
[Mathematica](https://mathworld.wolfram.com/FallingFactorial.html)
[SymPy](https://docs.sympy.org/latest/modules/functions/combinatorial.html#sympy.functions.combinatorial.factorials.FallingFactorial)
-/
@[main]
private lemma main
  [CommRing α]
-- given
  (x : α)
  (k : ℕ) :
-- imply
  descFactorial x k = ∏ i : Fin k, (x - i) := by
-- proof
  induction k with
  | zero =>
    simp [descFactorial]
  | succ k ih =>
    rw [descFactorial, descPochhammer_succ_eval, ← descFactorial, ih]
    rw [Fin.prod_univ_castSucc]
    simp


-- created on 2020-02-22
-- updated on 2026-09-06
