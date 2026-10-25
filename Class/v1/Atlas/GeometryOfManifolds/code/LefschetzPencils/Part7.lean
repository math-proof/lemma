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
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- Data for the **perturbation step** in symplectifying a branched cover: a closed
auxiliary 2-form $\alpha$ and parameter $\varepsilon \neq 0$ together with a
tangent splitting whose vertical kernel is annihilated by $\eta$ (the pullback
of the base symplectic form), $\alpha$ is non-degenerate on the kernel, and
$\eta + \varepsilon\alpha$ is non-degenerate on horizontal vectors. -/
class BranchedCoverPerturbationData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (η α : Ω 2) (ε : ℝ)
    extends TangentSplitting (inst := inst) α where
  ε_ne_zero : ε ≠ 0
  pullback_vanishes_on_K : ∀ (X : VF), inst.ι (projV X) η = 0
  alpha_nondeg_on_K : ∀ (X Y : VF),
    inst.ι (projV X) α = inst.ι (projV Y) α → projV X = projV Y
  complement_nondeg : ∀ (X Y : VF), projV X = projV Y →
    inst.ι X (η + ε • α) = inst.ι Y (η + ε • α) → X = Y
  alpha_closed : inst.d α = 0


