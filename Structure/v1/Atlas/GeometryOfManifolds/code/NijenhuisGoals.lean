/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
set_option autoImplicit false
set_option maxHeartbeats 800000

open DifferentialFormSpace


/-- Existence of holomorphic coordinates for an almost complex structure $J$: a chart $\varphi$
in which $J$ intertwines with a pointwise complex structure $J_{\mathrm{loc}}^*$ on 1-forms,
Lie brackets of vector fields pull back to act trivially on pulled-back forms, and pulled-back
forms separate vector fields. -/
structure HasHolomorphicCoords
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst)) : Prop where
  holo_coords :
    ∃ (Ω_loc : ℕ → Type) (VF_loc : Type)
      (inst_loc : DifferentialFormSpace Ω_loc VF_loc)
      (_J_loc : @AlmostComplexStr Ω_loc VF_loc inst_loc)
      (φ : @DFSMorphism Ω VF Ω_loc VF_loc inst inst_loc)
      (J_loc_star : Ω_loc 1 → Ω_loc 1),

      (∀ (X : VF) (α : Ω_loc 1),
        inst.ι (J.J X) (φ.pullback α) = inst.ι X (φ.pullback (J_loc_star α))) ∧

      (∀ (α : Ω_loc 1), J_loc_star (J_loc_star α) = -α) ∧


      (∀ (X Y : VF) (α_loc : Ω_loc 1),
        inst.ι (hbr.bracket X Y) (φ.pullback α_loc) = 0) ∧


      (∀ (Z : VF),
        (∀ (α_loc : Ω_loc 1), inst.ι Z (φ.pullback α_loc) = 0) →
        ∀ (β : Ω 1), inst.ι Z β = 0)

/-- An almost complex structure on a manifold: a pointwise endomorphism $J_x: T_x M \to T_x M$
with $J_x^2 = -\mathrm{id}$. -/
structure ACSOnMfd (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  J : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  sq_neg : ∀ (x : M) (v : TangentSpace I x), J x (J x v) = -v

