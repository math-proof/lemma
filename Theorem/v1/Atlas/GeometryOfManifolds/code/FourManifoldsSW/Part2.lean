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
public import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part7
open Manifold

set_option autoImplicit false

public section

noncomputable section

noncomputable section SpinCGroupSection

/-- $(-1)^2 = 1$ in the circle group. -/
theorem negOneCircle_sq : (negOneCircle : Circle) ^ 2 = 1 := by
  ext1; show (negOneCircle.1) ^ 2 = 1
  simp [negOneCircle, sq]

end SpinCGroupSection
end
