import Mathlib
import sympy.Basic
import Def.Algebra.Ring.JacobsonCommutativity
import Theorem.Algebra.Ring.JacobsonCommutativity
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

/--
[IsPrimeIdeal.ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Ring/JacobsonCommutativity.lean)
-/
@[path]
private lemma IsPrimeIdeal_ne_top_eq
  [Ring R]
  {P : TwoSidedIdeal R}
-- given
  (hP : Int.Ring.JacobsonCommutativity.IsPrimeIdeal P) :
-- imply
  P ≠ ⊤ := by
-- proof
  apply Int.Ring.JacobsonCommutativity.IsPrimeIdeal.ne_top hP

/--
[IsPrimeIdeal.mem_or_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Ring/JacobsonCommutativity.lean)
-/
@[path]
private lemma IsPrimeIdeal_mem_or_mem_eq
  [Ring R]
  {P : TwoSidedIdeal R} {a b : R}
-- given
  (hP : Int.Ring.JacobsonCommutativity.IsPrimeIdeal P)
  (h : ∀ r : R, a * r * b ∈ P) :
-- imply
  a ∈ P ∨ b ∈ P := by
-- proof
  apply Int.Ring.JacobsonCommutativity.IsPrimeIdeal.mem_or_mem hP h

-- created on 2026-10-09
-- updated on 2026-10-23
