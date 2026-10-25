/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- The twisted differential $d_C = -J d J: \Omega^p \to \Omega^{p+1}$ associated to
an action of $J$ on forms. -/
noncomputable def d_C_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))

/-- The codifferential twisted by $J$: $d_C^* = -J d^* J: \Omega^{p+1} \to \Omega^p$. -/
noncomputable def d_C_star_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : Codifferential (inst := inst))
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))


