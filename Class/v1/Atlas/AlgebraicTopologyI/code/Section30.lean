/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection
import Def.v1.Atlas.AlgebraicTopologyI.code.Section30
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
