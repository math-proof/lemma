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
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part7
open Manifold

set_option autoImplicit false


noncomputable section

noncomputable section SpinCGroupSection

/-- $(-1)^2 = 1$ in the circle group. -/
theorem negOneCircle_sq : (negOneCircle : Circle) ^ 2 = 1 := by
  ext1; show (negOneCircle.1) ^ 2 = 1
  simp [negOneCircle, sq]

end SpinCGroupSection
end
