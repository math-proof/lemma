import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DimensionDef
open TopologicalSpace Order Topology


/--
[dimension_eq_krullDim_irreducibleCloseds](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionDef.lean)
-/
@[path]
lemma dimension_eq_krullDim_irreducibleCloseds
  {X : Type*}
  [TopologicalSpace X] :
-- imply
  dimension X = krullDim (IrreducibleCloseds X) :=
-- proof
  rfl

/--
[dimension_le_of_isInducing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionDef.lean)
-/
@[path]
lemma dimension_le_of_isInducing
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : Y → X}
-- given
  (hf : IsInducing f) :
-- imply
  dimension Y ≤ dimension X :=
-- proof
  IsInducing.topologicalKrullDim_le hf

/--
[dimension_subspace_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionDef.lean)
-/
@[path]
lemma dimension_subspace_le
  {X : Type*}
  [TopologicalSpace X]
  {Y : Set X} :
-- imply
  dimension Y ≤ dimension X :=
-- proof
  topologicalKrullDim_subspace_le X Y

/--
[dimension_le_zero_of_discreteTopology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionDef.lean)
-/
@[path]
lemma dimension_le_zero_of_discreteTopology
  {X : Type*}
  [TopologicalSpace X]
  [DiscreteTopology X] :
-- imply
  dimension X ≤ 0 :=
-- proof
  topologicalKrullDim_zero_of_discreteTopology X


-- created on 2026-10-23
