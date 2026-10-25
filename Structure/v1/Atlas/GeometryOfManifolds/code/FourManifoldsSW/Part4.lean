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
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part3
open Manifold

set_option autoImplicit false


noncomputable section

/-- A formal Seiberg-Witten solution: bundles together a Dirac operator $D_A$, a positive
spinor $\psi \in \Gamma(S^+)$, the self-dual curvature $F_A^+ \in \Omega^{2,+}$, and the
analytic data (Weitzenböck and Bochner identities) needed for the a priori bounds:
$\langle D_A^2 \psi, \psi\rangle = \langle \nabla^*\nabla\psi, \psi\rangle +
\tfrac{s}{4}|\psi|^2 + \tfrac{1}{2}\langle \gamma(F_A^+)\psi, \psi\rangle$,
together with $D_A\psi = 0$ on the kernel. -/
structure SWSolution
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  dirac : DiracOperator spinc
  ψ : spinc.SectionsPlus
  F_A_plus : Ω2
  supNormSq : ℝ
  supNormSq_nonneg : 0 ≤ supNormSq
  supNormSq_eq : supNormSq = spinc.normSqPlus ψ
  scalarCurvatureVal : ℝ
  laplacianTerm : ℝ
  covDerivNormSq : ℝ
  laplacianTerm_nonneg : 0 ≤ laplacianTerm
  covDerivNormSq_nonneg : 0 ≤ covDerivNormSq
  connLapInnerProd : ℝ
  cliffordInnerProd : ℝ
  diracSqInnerProd : ℝ
  integration_by_parts_eq : connLapInnerProd = laplacianTerm + covDerivNormSq
  curvature_eq_applied : spinc.γ_on_2forms F_A_plus ψ = spinc.tracelessQuadratic ψ ψ
  clifford_inner_from_gamma :
    cliffordInnerProd = spinc.hermitianInnerPlus (spinc.γ_on_2forms F_A_plus ψ) ψ
  clifford_quadratic_eq : cliffordInnerProd = (1 / 2) * supNormSq ^ 2
  diracSq_diagonal_eq_connLap : ℝ
  diracSq_offdiagonal_eq_curvature : ℝ
  diagonal_eq : diracSq_diagonal_eq_connLap = connLapInnerProd
  offdiagonal_eq : diracSq_offdiagonal_eq_curvature =
    (scalarCurvatureVal / 4) * supNormSq + (1 / 2) * cliffordInnerProd
  diracSq_split : diracSqInnerProd = diracSq_diagonal_eq_connLap + diracSq_offdiagonal_eq_curvature
  dirac_kernel : diracSqInnerProd = 0

end
