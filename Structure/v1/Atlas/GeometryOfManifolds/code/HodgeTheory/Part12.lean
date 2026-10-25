/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part11
set_option autoImplicit false

open DifferentialFormSpace


/-- Compatibility data witnessing that $J$ commutes with each of $\partial, \bar\partial,
\partial^*, \bar\partial^*$ on a Kähler manifold. -/
structure KahlerJDolbeaultComm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    (dol_lap : DolbeaultLaplacian dol cod) where
  J_commutes_del : ∀ {p : ℕ} (α : Ω p), dol.del (Jf.J_form α) = Jf.J_form (dol.del α)
  J_commutes_delbar : ∀ {p : ℕ} (α : Ω p), dol.delbar (Jf.J_form α) = Jf.J_form (dol.delbar α)
  J_commutes_del_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.del_star (Jf.J_form α) = Jf.J_form (dol_lap.del_star α)
  J_commutes_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.delbar_star (Jf.J_form α) = Jf.J_form (dol_lap.delbar_star α)


