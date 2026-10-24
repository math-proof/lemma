import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Blowups


/--
[fiber_origin_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Blowups.lean)
-/
@[path]
lemma fiber_origin_dim
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (Polynomial k ⧸ Ideal.span {(Polynomial.X : Polynomial k) ^ 2 - 1}) = 2 := by
-- proof
  rwa [finrank_quotient_span_eq_natDegree]


-- created on 2026-10-23
