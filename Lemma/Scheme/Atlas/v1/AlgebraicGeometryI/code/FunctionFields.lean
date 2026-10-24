import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.FunctionFields
open Module Ideal


/--
[morphismDegree_eq_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FunctionFields.lean)
-/
@[path]
lemma morphismDegree_eq_finrank
  {B A : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [Algebra.IsAlgebraic B A] :
-- imply
  morphismDegree B A = finrank B A :=
-- proof
  Algebra.IsAlgebraic.finrank_of_isFractionRing B (FractionRing B) A (FractionRing A)
end FiberBound
section Ramification
end Ramification


-- created on 2026-10-23
