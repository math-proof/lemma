/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part11
set_option autoImplicit false

open DifferentialFormSpace


/-- The harmonic projection acts as the identity on $\bar\square$-harmonic forms. -/
def JActsOnForms.d_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))


/-- The twisted Laplacian $\Delta_C = -J \Delta J$ associated to the $J$-action on forms. -/
def JActsOnForms.laplacian_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  -(Jf.J_form (laplacian cod (Jf.J_form α)))

