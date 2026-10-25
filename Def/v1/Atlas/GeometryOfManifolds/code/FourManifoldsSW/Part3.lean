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
import Structure.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part3
open Manifold

set_option autoImplicit false


noncomputable section

section DiracOperatorSection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

variable {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]

variable {spinc : SpinCStructure M Ω1 Ω2}

/-- The local Dirac sum $D_A \psi = \sum_{i=1}^4 \gamma(e^i)\nabla^A_{e_i}\psi \in \Gamma(S^-)$. -/
def dirac_sum (D : DiracOperator spinc) (ψ : spinc.SectionsPlus) : spinc.SectionsMinus :=
  ∑ i : Fin 4, spinc.γ_plus_to_minus (D.frame i) (D.conn_plus i ψ)

/-- The local adjoint Dirac sum $D_A^- \varphi = \sum_i \gamma(e^i)\nabla^A_{e_i}\varphi
\in \Gamma(S^+)$ for $\varphi \in \Gamma(S^-)$. -/
def dirac_sum_adjoint (D : DiracOperator spinc) (φ : spinc.SectionsMinus) : spinc.SectionsPlus :=
  ∑ i : Fin 4, spinc.γ_minus_to_plus (D.frame i) (D.conn_minus i φ)

/-- The positive-chirality Dirac operator $D_A^+ : \Gamma(S^+) \to \Gamma(S^-)$. -/
def DiracOperator.D_plus (D : DiracOperator spinc) : spinc.SectionsPlus → spinc.SectionsMinus :=
  dirac_sum D

/-- The negative-chirality Dirac operator $D_A^- : \Gamma(S^-) \to \Gamma(S^+)$, the $L^2$
adjoint of $D_A^+$. -/
def DiracOperator.D_minus (D : DiracOperator spinc) : spinc.SectionsMinus → spinc.SectionsPlus :=
  dirac_sum_adjoint D

end DiracOperatorSection
end
