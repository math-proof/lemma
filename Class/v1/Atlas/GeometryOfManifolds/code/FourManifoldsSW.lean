/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Circle
import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW
open Manifold

set_option autoImplicit false


noncomputable section

/-- Typeclass recording the topology of a compact simply-connected 4-manifold $M$: its
intersection form $Q$ and Euler characteristic $\chi = 2 + b_2$. -/
class Has4ManifoldTopology
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  Q : IntersectionForm
  euler : ℤ
  euler_eq : euler = 2 + (Q.b₂ : ℤ)

end
