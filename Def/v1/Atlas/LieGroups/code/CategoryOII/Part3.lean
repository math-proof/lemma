/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryOII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Int.Surjective_Comp.of.Surjective
import Def.v1.Atlas.LieGroups.code.TensorHomAxiom
import Theorem.v1.Atlas.LieGroups.code.CategoryOII.Part2


def LieModule.CompositionSeriesOf.countFactorsIso
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs : LieModule.CompositionSeriesOf rd M)
    (L : Type*) [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] : ℕ :=
  Finset.card (Finset.univ.filter fun (i : Fin cs.length) =>
    Nonempty (L ≃ₗ⁅R, 𝔤⁆ (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)))

noncomputable def quotTopBotLieModuleEquiv
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L] :
    (↥(⊤ : LieSubmodule R 𝔤 L) ⧸
      ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl)) ≃ₗ⁅R,𝔤⁆ L := by
  have hbot_sub : ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule = ⊥ := by
    have h : (⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl = ⊥ := by
      rw [LieSubmodule.comap_incl_eq_bot]; simp
    simp [h]
  exact {
    ((⊥ : LieSubmodule R 𝔤 L).comap (⊤ : LieSubmodule R 𝔤 L).incl).toSubmodule.quotEquivOfEqBot
      hbot_sub |>.trans (LinearEquiv.ofTop (⊤ : Submodule R L) rfl) with
    map_lie' := by
      intro x q
      induction q using Quotient.inductionOn'
      rfl
  }

noncomputable def LieModuleHom.liftQ
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (f : P →ₗ⁅R, 𝔤⁆ L) (h : J ≤ f.ker) :
    (P ⧸ J) →ₗ⁅R, 𝔤⁆ L where
  toLinearMap := J.toSubmodule.liftQ f.toLinearMap (by
    intro x hx; exact LinearMap.mem_ker.mpr (LieModuleHom.mem_ker.mp (h hx)))
  map_lie' := by
    intro x m
    induction m using Quotient.inductionOn' with | h m =>
    show f ⁅x, m⁆ = ⁅x, f m⁆
    exact f.map_lie x m

noncomputable def homEquivThroughQuotient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {P : Type*} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    {L : Type*} [AddCommGroup L] [Module R L]
    [LieRingModule 𝔤 L] [LieModule R 𝔤 L]
    {J : LieSubmodule R 𝔤 P}
    (hfact : ∀ (f : P →ₗ⁅R, 𝔤⁆ L), J ≤ f.ker) :
    ((P ⧸ J) →ₗ⁅R, 𝔤⁆ L) ≃ₗ[R] (P →ₗ⁅R, 𝔤⁆ L) :=
  LinearEquiv.ofBijective
    { toFun := fun g => g.comp (LieSubmodule.Quotient.mk' J)
      map_add' := fun g₁ g₂ => by ext; simp
      map_smul' := fun r g => by ext; simp }
    ⟨by

      intro g₁ g₂ h
      ext ⟨m⟩
      exact LieModuleHom.congr_fun h m
    , by

      intro f
      exact ⟨LieModuleHom.liftQ f (hfact f), by
        ext p; rfl⟩
    ⟩

