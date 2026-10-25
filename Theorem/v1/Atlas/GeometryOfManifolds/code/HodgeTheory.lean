/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- Restatement of $2\bar\square = \Delta$ on Kähler manifolds (given as a hypothesis here)
in the form $\bar\square \alpha + \bar\square \alpha = \Delta \alpha$. -/
theorem box_bar_eq_half_laplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (_S : SymplecticManifold Ω VF)
    (_J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler _S _J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α
)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
  h_two_box_bar α


