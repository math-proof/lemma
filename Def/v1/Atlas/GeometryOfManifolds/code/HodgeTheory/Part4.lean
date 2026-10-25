/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- The $\bar\partial$-Laplacian $\bar\square = \bar\partial\bar\partial^* + \bar\partial^*\bar\partial$
on $(p,q)$-forms. -/
def DolbeaultLaplacian.box_bar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)

/-- The $\partial$-Laplacian $\square = \partial\partial^* + \partial^*\partial$. -/
def DolbeaultLaplacian.box
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)


