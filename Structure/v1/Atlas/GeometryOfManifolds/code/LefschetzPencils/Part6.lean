/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part6
public section

set_option autoImplicit false

open DifferentialFormSpace


/-- A **symplectic branched covering**: a symplectic target $(Y, \omega_Y)$, a covering
map $f: X \to Y$, and an integer degree $\geq 1$. -/
structure SymplecticBranchedCovering
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y] where
  target : SymplecticManifold Ω_Y VF_Y
  f : DFSMorphism Ω_X VF_X Ω_Y VF_Y
  degree : ℕ
  degree_pos : 0 < degree


