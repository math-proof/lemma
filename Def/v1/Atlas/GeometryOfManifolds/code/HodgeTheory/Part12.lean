/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
set_option autoImplicit false

open DifferentialFormSpace


/-- The twisted codifferential $d_C^* = -J d^* J$ as a method on `JActsOnForms`. -/
def JActsOnForms.d_C_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))


/-- A form is *smooth via Sobolev* if it lies in every Sobolev space $H^s$:
$\alpha \in C^\infty \iff \alpha \in \bigcap_s H^s$. -/
def IsSmoothViaSobolev
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    {p : ℕ} (α : Ω (p + 1)) : Prop :=
  ∀ s : ℕ, sob.IsSobolevRegular s α

