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
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part2
open Manifold

set_option autoImplicit false


noncomputable section

section DiracOperatorSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]

variable {spinc : SpinCStructure M Ω1 Ω2}

/-- Data of a Dirac operator $D_A = \sum_i \gamma(e^i)\nabla^A_{e_i}$ for a Spin-c structure:
a local frame $(e_i)$, covariant derivatives $\nabla^A_{e_i}$ on $S^\pm$, $\mathbb{R}$-linearity
of Clifford multiplication, and the $L^2$ adjoint relation between $D_A^+ : \Gamma(S^+) \to \Gamma(S^-)$
and $D_A^- : \Gamma(S^-) \to \Gamma(S^+)$. -/
structure DiracOperator (spinc : SpinCStructure M Ω1 Ω2) where
  frame : Fin 4 → Ω1
  conn_plus : Fin 4 → spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus
  conn_minus : Fin 4 → spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus
  γ_linear : ∀ (ω : Ω1), IsLinearMap ℝ (spinc.γ_plus_to_minus ω)
  γ_linear_minus : ∀ (ω : Ω1), IsLinearMap ℝ (spinc.γ_minus_to_plus ω)
  L2pairingPlus : spinc.SectionsPlus → spinc.SectionsPlus → ℝ
  L2pairingMinus : spinc.SectionsMinus → spinc.SectionsMinus → ℝ
  adjoint_relation : ∀ (ψ : spinc.SectionsPlus) (φ : spinc.SectionsMinus),
    L2pairingMinus
      (∑ i : Fin 4, spinc.γ_plus_to_minus (frame i) (conn_plus i ψ)) φ =
    L2pairingPlus ψ
      (∑ i : Fin 4, spinc.γ_minus_to_plus (frame i) (conn_minus i φ))

end DiracOperatorSection
end
