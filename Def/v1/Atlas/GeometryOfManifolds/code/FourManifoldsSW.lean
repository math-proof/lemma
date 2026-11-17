/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Circle
public import Class.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW

@[expose] public section

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
