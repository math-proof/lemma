/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
set_option autoImplicit false

open DifferentialFormSpace


/-- A line bundle $L$ is ample if its curvature form is nondegenerate, i.e.
$X \mapsto \iota_X R^\nabla$ is injective. Geometrically this expresses
positivity of $c_1(L)$. -/
class IsAmple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : LineBundleData (inst := inst)) : Prop where
  positive_curvature : Function.Injective (fun (X : VF) => inst.ι X L.curvature)

/-- A line bundle is very ample if its global sections separate points,
giving an embedding into projective space; the curvature is still positive
and there exist nontrivial sections distinguishing points. -/
class IsVeryAmple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : LineBundleData (inst := inst)) : Prop where
  sections_give_embedding : Function.Injective (fun (X : VF) => inst.ι X L.curvature)
  has_sections : ∃ (s₁ s₂ : Ω 0), s₁ ≠ s₂ ∧ inst.d s₁ ≠ inst.d s₂


/-- A $2$-form $\omega$ is a Kähler form if it is closed ($d\omega = 0$) and
nondegenerate ($X \mapsto \iota_X \omega$ is injective). -/
class IsKahlerForm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (ω : Ω 2) : Prop where
  closed : inst.d ω = 0
  nondegenerate : Function.Injective (fun (X : VF) => inst.ι X ω)


