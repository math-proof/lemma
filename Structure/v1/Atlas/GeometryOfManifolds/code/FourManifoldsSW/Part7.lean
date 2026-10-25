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
import Theorem.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW
open Manifold

set_option autoImplicit false


noncomputable section

/-- The Seiberg-Witten moduli space $\mathcal{M}(S, g, \mu) = \{(A,\psi)\}/\mathcal{G}$ together
with its expected dimension $d(S)$, total point count, and a well-defined signed count for the
zero-dimensional case (whose absolute value is bounded by the cardinality). -/
structure SWModuliSpace
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [Zero spinc.SectionsMinus] where
  gauge : GaugeActionData spinc
  quotientType : Type
  quotientProj : SWSolution spinc → quotientType
  sol_is_solution : ∀ (sol : SWSolution spinc), IsSWSolution sol
  proj_faithful : ∀ (sol₁ sol₂ : SWSolution spinc),
    quotientProj sol₁ = quotientProj sol₂ ↔ GaugeEquiv gauge sol₁ sol₂
  expectedDim : ℤ
  numPoints : ℕ
  signedCount : ℤ
  signedCount_bound : signedCount.natAbs ≤ numPoints

/-- Axiomatic data for the Seiberg-Witten invariant $\mathrm{SW} : \mathrm{Spin}^c(M) \to \mathbb{Z}$
on a compact 4-manifold $M$ with $b_2^+ \geq 1$: $\mathrm{SW}$ vanishes when the moduli space is
empty, equals the signed count in the zero-dimensional case, has finite support, and depends only
on $c_1(L)$. -/
structure HasSWInvariant
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ω1 Ω2 : Type*) [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M] where
  b₂_plus_pos : htop.Q.b₂_plus ≥ 1
  SW : SpinCStructure M Ω1 Ω2 → ℤ
  SW_empty : ∀ (spinc : SpinCStructure M Ω1 Ω2) [Zero spinc.SectionsMinus],
    (∀ (sol : SWSolution spinc), ¬ IsSWSolution sol) → SW spinc = 0
  SW_count_dim_zero : ∀ (spinc : SpinCStructure M Ω1 Ω2) [Zero spinc.SectionsMinus]
    (Mod : SWModuliSpace spinc), Mod.expectedDim = 0 → SW spinc = Mod.signedCount
  SW_finiteness : Set.Finite {spinc : SpinCStructure M Ω1 Ω2 | SW spinc ≠ 0}
  SW_of_c₁ : ℤ → ℤ
  SW_eq_SW_of_c₁ : ∀ (spinc : SpinCStructure M Ω1 Ω2), SW spinc = SW_of_c₁ spinc.c₁_L


end
