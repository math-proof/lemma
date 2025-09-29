import sympy.core.power
import sympy.Basic


/--
This lemma establishes an equivalence between two inequalities involving a non-negative real number `x` and a real number `y`.
Specifically, it states that for `x ≥ 0`, the inequality `x < √y` holds if and only if `x² < y`.
This equivalence is fundamental in algebraic manipulations where converting between square roots and squared terms is necessary, ensuring validity under the non-negativity condition of `x`.
-/
@[main]
private lemma main
  {x y : ℝ}
-- given
  (hx : x ≥ 0) :
-- imply
  x < √y ↔ x² < y :=
-- proof
  Real.lt_sqrt hx


-- created on 2025-03-25
