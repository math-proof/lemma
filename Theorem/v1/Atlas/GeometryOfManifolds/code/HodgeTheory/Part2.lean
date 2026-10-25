/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- On a Kähler manifold, the Laplacian $\Delta$ preserves the Hodge $(p,q)$ bigrading,
deduced from the fact that $\bar\square$ preserves it and $\Delta = 2\bar\square$. -/
theorem laplacian_preserves_bidegree
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J' : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J')
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n)

    (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α)
    (k : ℕ) (p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q') :
    ∃ ω' : bg.Ω_pq p' q',
      cast (congrArg Ω h) (bg.incl p' q' ω') =
        laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) := by

  obtain ⟨ω₁, hω₁⟩ := h_box_bar_pres k p' q' h ω


  have hΔ : laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) =
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) +
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) :=
    (box_bar_eq_half_laplacian S J' hK dol_lap (h_two_box_bar := h_two_box_bar) _).symm

  rw [← hω₁] at hΔ

  refine ⟨bg.pq_add p' q' ω₁ ω₁, ?_⟩

  rw [hΔ]

  have h_add : bg.incl p' q' (bg.pq_add p' q' ω₁ ω₁) =
    bg.incl p' q' ω₁ + bg.incl p' q' ω₁ := bg.incl_add p' q' ω₁ ω₁

  have h_cast_add : ∀ {m n : ℕ} (heq : m = n) (a b : Ω m),
    cast (congrArg Ω heq) (a + b) = cast (congrArg Ω heq) a + cast (congrArg Ω heq) b := by
    intro m n heq; subst heq; intros; rfl
  rw [h_add, h_cast_add h]


