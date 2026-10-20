import Mathlib.NumberTheory.FLT.Basic
import sympy.Basic


/--
Fermat's Last Theorem. The py statement omitted `x y z ≠ 0` (fails at `0^n + 1^n = 1^n`).
Mathlib defines `FermatLastTheorem` but does not prove it; we take it as a hypothesis.
-/
@[path]
private lemma fermat.last_theorem
  {n x y z : ℕ}
-- given
  (hn : n ≥ 3)
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (hFLT : FermatLastTheorem) :
-- imply
  x ^ n + y ^ n ≠ z ^ n :=
-- proof
  hFLT n hn x y z hx hy hz


-- created on 2021-08-26
