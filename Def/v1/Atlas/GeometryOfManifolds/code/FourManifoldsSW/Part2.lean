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
public import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part2

@[expose] public section

open Manifold

set_option autoImplicit false


noncomputable section

/-- The traceless quadratic form $(\psi^* \otimes \varphi)_0 = \langle \psi, \varphi\rangle \cdot \psi
- \tfrac{1}{2}|\psi|^2 \cdot \varphi$, appearing on the right-hand side of the curvature equation
$\gamma(F_A^+) = (\psi^* \otimes \psi)_0$ in the Seiberg-Witten equations. -/
noncomputable def SpinCStructure.tracelessQuadratic
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) (ψ φ : spinc.SectionsPlus)
    : spinc.SectionsPlus :=
  (spinc.hermitianInnerPlus ψ φ) • ψ - ((1/2 : ℝ) * spinc.normSqPlus ψ) • φ


end
