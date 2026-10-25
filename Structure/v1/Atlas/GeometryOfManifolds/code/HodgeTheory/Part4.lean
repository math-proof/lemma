/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- Wells' anticommutation identities for the Dolbeault adjoint operators on a Kähler
manifold: $\partial\bar\partial^* + \bar\partial^*\partial = 0$ and
$\bar\partial\partial^* + \partial^*\bar\partial = 0$, plus an expansion identity. -/
structure KahlerWellsIdentities
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod) where
  del_delbar_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0
  delbar_del_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0
  wells_expansion : ∀ {p : ℕ} (α : Ω (p + 1)),
    (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
    (dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α)) -
    (dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α)) -
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)) = 0


