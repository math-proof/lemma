/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Ring/JacobsonCommutativity.lean -/


import Def.Algebra.Ring.JacobsonCommutativity


namespace MathlibExt.Algebra.Ring.JacobsonCommutativity

-- Exact-signature API invocation: generic `Ring` with pointwise exponent hypothesis.
example {R : Type*} [Ring R]
    (h : ∀ x : R, ∃ n : Nat, 1 < n ∧ x ^ n = x) :
    ∀ x y : R, x * y = y * x :=
  jacobson_commutativity h

end MathlibExt.Algebra.Ring.JacobsonCommutativity
