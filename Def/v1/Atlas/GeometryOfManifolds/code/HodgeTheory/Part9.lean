/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part9
set_option autoImplicit false

open DifferentialFormSpace


/-- Packages a Fredholm operator on $\Omega^{p+1}$ as an $\mathbb{R}$-linear map. -/
def IsFredholm.toLinearMap
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)}
    (hF : IsFredholm (inst := inst) L) (p : ℕ) : Ω (p + 1) →ₗ[ℝ] Ω (p + 1) :=
  { toFun := L
    map_add' := hF.L_add
    map_smul' := hF.L_smul }


