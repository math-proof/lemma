/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
public import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part5
public section

set_option autoImplicit false

open DifferentialFormSpace


/-- **Gompf's realization theorem for fundamental groups.**

Every finitely presented group $G$ arises as the fundamental group $\pi_1(S)$ of some
compact symplectic 4-manifold $S$. -/
structure HasHandlebodyDecomposition
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] : Prop where
  handle_data : ∃ (n₀ _n₁ n₂ _n₃ n₄ : ℕ),
    n₀ = 1 ∧ n₄ = 1 ∧ 0 < n₂

/-- Carrier for an Euler characteristic value $\chi \in \mathbb{Z}$. -/
structure HasEulerCharacteristic
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF] where
  euler : ℤ


