module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part5
public section
set_option autoImplicit false

open DifferentialFormSpace

/-- A pullback morphism $\varphi$ is **$\omega$-tame** if the pulled-back form
$\varphi^*\omega$ is non-degenerate on contraction. -/
class IsOmegaTame
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (φ : DFSMorphism Ω VF Ω VF) : Prop where
  taming_nondeg : Function.Injective (fun (v : VF) => inst.ι v (φ.pullback S.ω))

