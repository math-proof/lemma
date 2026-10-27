import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.LinearAlgebra.Lagrange

/--
[Lagrange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/Lagrange.lean)
-/
@[path]
private lemma eval_basis_self_eq
-- given
  {n : ℕ}
  {x : Fin n → ℝ}
  (hx : Function.Injective x)
  (k : Fin n) :
-- imply
  Lagrange.evalBasis x k (x k) = 1 := by
-- proof
  apply Lagrange.evalBasis_self x hx k

/--
[Lagrange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/Lagrange.lean)
-/
@[path]
private lemma eval_basis_of_ne_eq
-- given
  {n : ℕ}
  {x : Fin n → ℝ}
  {k j : Fin n}
  (hkj : k ≠ j) :
-- imply
  Lagrange.evalBasis x k (x j) = 0 := by
-- proof
  apply Lagrange.evalBasis_of_ne x hkj

/--
[Lagrange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/Lagrange.lean)
-/
@[path]
private lemma eval_interpolant_at_node_eq
-- given
  {n : ℕ}
  {x : Fin n → ℝ}
  (hx : Function.Injective x)
  (f : ℝ → ℝ)
  (j : Fin n) :
-- imply
  Lagrange.evalInterpolant x f (x j) = f (x j) := by
-- proof
  apply Lagrange.evalInterpolant_at_node x hx f j

/--
[Lagrange](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Polynomial/Lagrange.lean)
-/
@[path]
private lemma lebesgue_function_at_node_eq
-- given
  {n : ℕ}
  {x : Fin n → ℝ}
  (hx : Function.Injective x)
  (j : Fin n) :
-- imply
  Lagrange.lebesgueFunction x (x j) = 1 := by
-- proof
  apply Lagrange.lebesgueFunction_at_node x hx j

-- created on 2026-10-10
