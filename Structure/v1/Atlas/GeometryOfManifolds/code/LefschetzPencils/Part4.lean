/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- **Donaldson's theorem on Lefschetz pencils.**

For any compact symplectic 4-manifold $(M^4, \omega)$, after blowing up finitely many
points the resulting manifold $\hat M$ admits a Lefschetz fibration to $S^2$. -/
structure FiberSum.DFS
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    {Ω_Q : ℕ → Type*} {VF_Q : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    [inst_Q : DifferentialFormSpace Ω_Q VF_Q]
    [dim_M₁ : SymplecticManifoldDim Ω₁ VF₁]
    [dim_M₂ : SymplecticManifoldDim Ω₂ VF₂]
    [dim_Q : SymplecticManifoldDim Ω_Q VF_Q]
    [IsCompactManifold Ω_Q VF_Q] where
  M₁ : SymplecticManifold Ω₁ VF₁
  M₂ : SymplecticManifold Ω₂ VF₂
  Q : SymplecticManifold Ω_Q VF_Q
  ι₁ : DFSMorphism Ω_Q VF_Q Ω₁ VF₁
  ι₂ : DFSMorphism Ω_Q VF_Q Ω₂ VF₂
  ι₁_symplectic : ι₁.pullback M₁.ω = Q.ω
  ι₂_symplectic : ι₂.pullback M₂.ω = Q.ω
  codim_two_M₁ : dim_Q.n + 1 = dim_M₁.n
  codim_two_M₂ : dim_Q.n + 1 = dim_M₂.n
  normalBundleTriv_M₁ : ∃ (η : Ω₁ 2),
    inst₁.d η = 0 ∧ ι₁.pullback η = 0 ∧ η ≠ 0
  normalBundleTriv_M₂ : ∃ (η : Ω₂ 2),
    inst₂.d η = 0 ∧ ι₂.pullback η = 0 ∧ η ≠ 0


