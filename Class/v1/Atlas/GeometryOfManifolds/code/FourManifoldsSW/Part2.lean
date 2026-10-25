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
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW
open Manifold

set_option autoImplicit false


noncomputable section

/-- Typeclass for a compact (simply connected) 4-manifold $M$. -/
class IsCompactSimplyConnected4Manifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] : Prop where
  compact : CompactSpace M

/-- Two 4-manifolds have the same homeomorphism type (à la Freedman) if their intersection
forms agree in rank, signature, and parity. -/
class AreHomeomorphic4Manifolds
    (M₁ M₂ : Type*)
    [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₁]
    [TopologicalSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M₂]
    [htop₁ : Has4ManifoldTopology M₁] [htop₂ : Has4ManifoldTopology M₂] where
  b₂_eq : htop₁.Q.b₂ = htop₂.Q.b₂
  signature_eq : htop₁.Q.signature = htop₂.Q.signature
  parity_eq : htop₁.Q.isEven = htop₂.Q.isEven


end
