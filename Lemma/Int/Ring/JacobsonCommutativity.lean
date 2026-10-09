import Mathlib
import sympy.Basic
import sympy.Algebra.Ring.JacobsonCommutativity

/--
[jacobson_commutativity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Ring/JacobsonCommutativity.lean)
-/
@[path]
private lemma jacobson_commutativity_eq
-- given
  {R : Type*} [Ring R]
  (h : ∀ x : R, ∃ n : ℕ, 1 < n ∧ x ^ n = x) :
-- imply
  (∀ x y : R, x * y = y * x) :=
-- proof
  Int.Ring.JacobsonCommutativity.jacobson_commutativity h


-- created on 2026-10-09
