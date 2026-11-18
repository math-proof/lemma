module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Projection
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section30
public section
open Matrix

namespace SymmetricBilinearForms

/-- Definition 30.1: a *topological manifold* is a Hausdorff space that is
locally homeomorphic to some Euclidean space at every point (the dimension
may a priori depend on the point). -/
class IsTopologicalManifold (M : Type*) [TopologicalSpace M] : Prop where
  hausdorff : T2Space M
  locally_euclidean : ∀ x : M, ∃ n : ℕ, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))

/-- A *topological `n`-manifold*: a Hausdorff space equipped with a charted
space structure modelled on `ℝⁿ`. This is the dimension-fixed variant of
`IsTopologicalManifold`. -/
class TopologicalManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    extends ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  [hausdorff : T2Space M]

end SymmetricBilinearForms
