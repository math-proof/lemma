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
public import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part4
open Manifold

set_option autoImplicit false


public noncomputable section

/-- The perturbed Seiberg-Witten equations $D_A \psi = 0$ and
$\gamma(F_A^+) = (\psi^*\otimes\psi)_0 + \gamma(\mu)$ with perturbation $\mu \in \Omega^{2,+}$. -/
structure IsSWSolutionWith
    (sol : SWSolution spinc)
    (μ : Ω2) : Prop where
  dirac_eq : sol.dirac.D_plus sol.ψ = 0
  curvature_eq : ∀ (φ : spinc.SectionsPlus),
    spinc.γ_on_2forms sol.F_A_plus φ =
      spinc.tracelessQuadratic sol.ψ φ + spinc.γ_on_2forms μ φ

/-- The unperturbed Seiberg-Witten equations $D_A \psi = 0$ and
$\gamma(F_A^+) = (\psi^*\otimes\psi)_0$. -/
structure IsSWSolution
    (sol : SWSolution spinc) : Prop where
  dirac_eq : sol.dirac.D_plus sol.ψ = 0
  curvature_eq : ∀ (φ : spinc.SectionsPlus),
    spinc.γ_on_2forms sol.F_A_plus φ = spinc.tracelessQuadratic sol.ψ φ


/-- Abstract data of a gauge group $\mathcal{G}$ acting on Seiberg-Witten solutions
$(A,\psi) \mapsto (A - 2df \cdot f^{-1}, f\psi)$: the group, its action on solutions and on
$\psi, F_A^+$, compatibility with the group structure, preservation of $|\psi|^2$, and the
condition that the action is free away from reducibles. -/
structure GaugeActionData
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  GaugeGroup : Type
  [gaugeGroupGroup : Group GaugeGroup]
  gauge_action : GaugeGroup → SWSolution spinc → SWSolution spinc
  gauge_transform_spinor : GaugeGroup → spinc.SectionsPlus → spinc.SectionsPlus
  gauge_transform_curvature : GaugeGroup → Ω2 → Ω2
  spinor_formula : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).ψ = gauge_transform_spinor f sol.ψ
  curvature_formula : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).F_A_plus = gauge_transform_curvature f sol.F_A_plus
  gauge_action_one : ∀ (sol : SWSolution spinc), gauge_action 1 sol = sol
  gauge_action_mul : ∀ (f g : GaugeGroup) (sol : SWSolution spinc),
    gauge_action (f * g) sol = gauge_action f (gauge_action g sol)
  gauge_action_preserves_supNormSq : ∀ (f : GaugeGroup) (sol : SWSolution spinc),
    (gauge_action f sol).supNormSq = sol.supNormSq
  gauge_nontrivial : ∃ (f : GaugeGroup), f ≠ 1
  gauge_free_on_irreducible : ∀ (sol : SWSolution spinc),
    ¬sol.isReducible → ∀ (f : GaugeGroup), gauge_action f sol = sol → f = 1

end
