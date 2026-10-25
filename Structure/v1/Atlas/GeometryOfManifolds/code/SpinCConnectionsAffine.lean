/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SpinCConnectionsAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.FourManifoldsSW.Part8
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.FourManifoldsSW
set_option autoImplicit false


/-- A spin-c connection on a spin-c structure: a pair of additive connections
$\nabla^\pm$ on the positive/negative spinor bundles $S^\pm$, compatible with Clifford
multiplication in the Leibniz sense
$\nabla^-_v(\gamma(u)\psi) = \gamma(u)(\nabla^+_v\psi)$. -/
structure SpinCConnection
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  nabla_plus : Ω1 → spinc.SectionsPlus → spinc.SectionsPlus
  nabla_minus : Ω1 → spinc.SectionsMinus → spinc.SectionsMinus
  nabla_plus_add : ∀ (v : Ω1) (ψ₁ ψ₂ : spinc.SectionsPlus),
    nabla_plus v (ψ₁ + ψ₂) = nabla_plus v ψ₁ + nabla_plus v ψ₂
  nabla_minus_add : ∀ (v : Ω1) (φ₁ φ₂ : spinc.SectionsMinus),
    nabla_minus v (φ₁ + φ₂) = nabla_minus v φ₁ + nabla_minus v φ₂
  leibniz_clifford : ∀ (v u : Ω1) (ψ : spinc.SectionsPlus),
    nabla_minus v (spinc.γ_plus_to_minus u ψ) =
      spinc.γ_plus_to_minus u (nabla_plus v ψ)


/-- The "difference" of two spin-c connections is recorded by a real $1$-form $a$ together
with an imaginary factor $i$, so two spin-c connections differ by $i a \otimes \mathrm{id}_{S^\pm}$. -/
structure SpinCConnectionDifference
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2) where
  a : Ω1
  imaginary_factor : ℂ := Complex.I


