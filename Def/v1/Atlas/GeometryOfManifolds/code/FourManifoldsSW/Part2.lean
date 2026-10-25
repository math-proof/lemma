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
import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part2
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
