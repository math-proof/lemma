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
import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part5
open Manifold

set_option autoImplicit false


noncomputable section

/-- The Clifford module isomorphisms relating differential forms and spinor endomorphisms
on a Spin-c 4-manifold: the decomposition $\Omega^2 = \Omega^{2,+} \oplus \Omega^{2,-}$,
the full Clifford equivalence
$\Omega^0 \oplus \Omega^1 \oplus \Omega^2 \oplus \Omega^3 \oplus \Omega^4 \simeq
\mathrm{End}(S^+ \oplus S^-)$, and its even/odd splittings, together with the
$\mathrm{End}(S^\pm) \simeq \mathbb{C} \oplus \Omega^{2,\pm}$ decompositions. -/
structure CliffordIsomorphisms
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 Ω0 Ω3 Ω4 : Type*}
    [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [AddCommGroup Ω0] [Module ℝ Ω0] [AddCommGroup Ω3] [Module ℝ Ω3]
    [AddCommGroup Ω4] [Module ℝ Ω4]
    (spinc : SpinCStructure M Ω1 Ω2) where
  [instModCPlus : Module ℂ spinc.SectionsPlus]
  [instModCMinus : Module ℂ spinc.SectionsMinus]
  Ω2plus : Type
  Ω2minus : Type
  [instΩ2plus_acg : AddCommGroup Ω2plus]
  [instΩ2plus_mod : Module ℝ Ω2plus]
  [instΩ2minus_acg : AddCommGroup Ω2minus]
  [instΩ2minus_mod : Module ℝ Ω2minus]
  incl_plus : Ω2plus →ₗ[ℝ] Ω2
  incl_minus : Ω2minus →ₗ[ℝ] Ω2
  self_dual_condition : ∀ (ω : Ω2plus),
    IsSelfDual spinc.hodge_star (incl_plus ω)
  anti_self_dual_condition : ∀ (ω : Ω2minus),
    IsAntiSelfDual spinc.hodge_star (incl_minus ω)
  γ_full_equiv :
    (Ω0 × Ω1 × Ω2 × Ω3 × Ω4) ≃ₗ[ℝ]
    ((spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus)) ×
    ((spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsMinus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsPlus))
  even_clifford_equiv : (Ω0 × Ω2 × Ω4) ≃ₗ[ℝ]
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus)
  odd_clifford_equiv : (Ω1 × Ω3) ≃ₗ[ℝ]
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsMinus) × (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsPlus)
  endSplus_decomp :
    (spinc.SectionsPlus →ₗ[ℝ] spinc.SectionsPlus) ≃ₗ[ℝ] ℂ × Ω2plus
  endSminus_decomp :
    (spinc.SectionsMinus →ₗ[ℝ] spinc.SectionsMinus) ≃ₗ[ℝ] ℂ × Ω2minus


end
