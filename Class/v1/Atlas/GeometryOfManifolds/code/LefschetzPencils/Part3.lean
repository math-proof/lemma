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
public import Def.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils
public section
set_option autoImplicit false

open DifferentialFormSpace

/-- An orientation on a differential-form space: a fixed top-degree dimension,
a nowhere-vanishing closed volume form. -/
class IsOriented
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  dim : ℕ
  volumeForm : Ω dim
  volumeForm_ne_zero : volumeForm ≠ 0
  volumeForm_closed : inst.d volumeForm = 0

