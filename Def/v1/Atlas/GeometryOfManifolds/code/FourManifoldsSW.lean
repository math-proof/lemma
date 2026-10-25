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
import Class.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW
open Manifold

set_option autoImplicit false


noncomputable section

/-- $Q$ is positive definite, i.e. $b_2^- = 0$. -/
def IntersectionForm.IsPositiveDefinite (Q : IntersectionForm) : Prop := Q.b₂_minus = 0

/-- $Q$ is negative definite, i.e. $b_2^+ = 0$. -/
def IntersectionForm.IsNegativeDefinite (Q : IntersectionForm) : Prop := Q.b₂_plus = 0

/-- $Q$ is definite if it is either positive definite or negative definite. -/
def IntersectionForm.IsDefinite (Q : IntersectionForm) : Prop :=
  Q.IsPositiveDefinite ∨ Q.IsNegativeDefinite

/-- $Q$ is (potentially) diagonalisable in the sense that its parity is odd. -/
def IntersectionForm.IsDiagonal (Q : IntersectionForm) : Prop := Q.isEven = false

end
