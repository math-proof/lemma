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
import Class.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part2
open Manifold

set_option autoImplicit false


noncomputable section

/-- Abstract data for a $\mathrm{Spin}^c$-structure $S$ on a 4-manifold $M$: positive and
negative spinor bundle sections $\Gamma(S^\pm)$, the determinant line $L$ with $c_1(L)$,
Clifford multiplication $\gamma$ acting between $S^\pm$ and on 2-forms (with the
$(\pm 1)$-eigenspace decomposition under Hodge $*$), and a Hermitian inner product on $S^+$. -/
structure SpinCStructure
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (Ω1 : Type*) (Ω2 : Type*)
    [AddCommGroup Ω1] [Module ℝ Ω1]
    [AddCommGroup Ω2] [Module ℝ Ω2] where
  SectionsPlus : Type
  SectionsMinus : Type
  [instACGPlus : AddCommGroup SectionsPlus]
  [instModPlus : Module ℝ SectionsPlus]
  [instACGMinus : AddCommGroup SectionsMinus]
  [instModMinus : Module ℝ SectionsMinus]
  nontrivial_plus : Nontrivial SectionsPlus
  c₁_L : ℤ
  Q_eval : ℤ → ℤ
  c₁_pair : ℤ → ℤ
  metric_pairing : Ω1 → Ω1 → ℝ
  γ_plus_to_minus : Ω1 → SectionsPlus → SectionsMinus
  γ_minus_to_plus : Ω1 → SectionsMinus → SectionsPlus
  γ_on_2forms : Ω2 → SectionsPlus → SectionsPlus
  γ_on_2forms_minus : Ω2 → SectionsMinus → SectionsMinus
  hodge_star : Ω2 → Ω2
  hodge_star_invol : ∀ (α : Ω2), hodge_star (hodge_star α) = α
  hodge_clifford_plus : ∀ (α : Ω2) (ψ : SectionsPlus),
    γ_on_2forms (hodge_star α) ψ = γ_on_2forms α ψ
  hodge_clifford_minus : ∀ (α : Ω2) (ψ : SectionsMinus),
    γ_on_2forms_minus (hodge_star α) ψ = -γ_on_2forms_minus α ψ
  gamma_anticomm : ∀ (u v : Ω1) (ψ : SectionsPlus),
    γ_minus_to_plus u (γ_plus_to_minus v ψ) + γ_minus_to_plus v (γ_plus_to_minus u ψ) =
      (-2 * metric_pairing u v) • ψ
  hermitianInnerPlus : SectionsPlus → SectionsPlus → ℝ
  normSqPlus : SectionsPlus → ℝ
  normSq_nonneg : ∀ (ψ : SectionsPlus), 0 ≤ normSqPlus ψ
  normSq_zero_iff : ∀ (ψ : SectionsPlus), normSqPlus ψ = 0 ↔ ψ = 0
  hermitian_norm_compat : ∀ (ψ : SectionsPlus), hermitianInnerPlus ψ ψ = normSqPlus ψ
  hermitian_smul_left : ∀ (c : ℝ) (ψ φ : SectionsPlus),
    hermitianInnerPlus (c • ψ) φ = c * hermitianInnerPlus ψ φ

end
