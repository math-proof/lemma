import Mathlib
import sympy.Basic


/--
[LinearEquiv.ofEq_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/ExtendingIsometries.lean)
-/
@[path]
private lemma main
  [Semiring R]
  [AddCommMonoid M]
  [Module R M]
  {p q : Submodule R M}
  {x : p}
-- given
  (h : p = q) :
-- imply
  (LinearEquiv.ofEq p q h x : M) = (x : M) := by
-- proof
  subst h
  rfl


-- created on 2026-10-23
-- updated on 2026-10-24
