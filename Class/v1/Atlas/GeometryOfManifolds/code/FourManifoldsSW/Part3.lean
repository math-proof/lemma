module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/FourManifoldsSW.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Circle
public import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part7
public section

open Manifold

set_option autoImplicit false


noncomputable section

/-- Typeclass recording a scalar curvature value $s$ for the Riemannian metric on $M$. -/
class HasScalarCurvature
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] where
  scalarCurvature : ℝ

end
