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
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part6
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


