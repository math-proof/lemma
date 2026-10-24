import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec4Dimension
open TopologicalSpace


/--
[noetherianTopologicalDim_eq_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Dimension.lean)
-/
@[path]
lemma noetherianTopologicalDim_eq_krullDim
  {X : Type*}
  [TopologicalSpace X]
  [TopologicalSpace.NoetherianSpace X] :
-- imply
  noetherianTopologicalDim X = Order.krullDim (IrreducibleCloseds X) :=
-- proof
  rfl

/--
[noetherianTopologicalDim_eq_topologicalKrullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4Dimension.lean)
-/
@[path]
lemma noetherianTopologicalDim_eq_topologicalKrullDim
  {X : Type*}
  [TopologicalSpace X]
  [TopologicalSpace.NoetherianSpace X] :
-- imply
  noetherianTopologicalDim X = topologicalKrullDim X :=
-- proof
  rfl


-- created on 2026-10-23
