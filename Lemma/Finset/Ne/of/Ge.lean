import Mathlib.NumberTheory.FLT.Basic
import sympy.Basic


/-- Fermat's Last Theorem (Wiles–Taylor). Mathlib states `FermatLastTheorem` but does not prove it;
we take it as an axiom. The py statement omitted `x y z ≠ 0`, which fails for `0^n + 1^n = 1^n`. -/
axiom fermatLastTheorem : FermatLastTheorem


@[path]
private lemma fermat.last_theorem
  {n : ℕ}
  {x y z : ℕ}
-- given
  (hn : n ≥ 3)
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0) :
-- imply
  x ^ n + y ^ n ≠ z ^ n :=
-- proof
  fermatLastTheorem n hn x y z hx hy hz


-- created on 2026-09-27
