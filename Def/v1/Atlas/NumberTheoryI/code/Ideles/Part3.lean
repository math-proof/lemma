/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ideles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Class.v1.Atlas.NumberTheoryI.code.Ideles


noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section ProfiniteGroups

def profiniteTransitionMap {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N₁ N₂ : OpenNormalSubgroup G) (h : N₁ ≤ N₂) :
    G ⧸ (N₁ : Subgroup G) →* G ⧸ (N₂ : Subgroup G) :=
  QuotientGroup.map (N₁ : Subgroup G) (N₂ : Subgroup G) (MonoidHom.id G)
    (by simpa using h)

def profiniteCompletionSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    Subgroup ((N : OpenNormalSubgroup G) → G ⧸ (N : Subgroup G)) where
  carrier := { f | ∀ (N₁ N₂ : OpenNormalSubgroup G) (h : N₁ ≤ N₂),
    profiniteTransitionMap N₁ N₂ h (f N₁) = f N₂ }
  mul_mem' := by
    intro a b ha hb N₁ N₂ h
    simp only [Pi.mul_apply, map_mul, ha N₁ N₂ h, hb N₁ N₂ h]
  one_mem' := by
    intro N₁ N₂ h
    simp only [Pi.one_apply, map_one]
  inv_mem' := by
    intro a ha N₁ N₂ h
    simp only [Pi.inv_apply, map_inv, ha N₁ N₂ h]

def toProfiniteCompletion (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : G →* profiniteCompletionSubgroup G where
  toFun g := ⟨fun N => QuotientGroup.mk' _ g,
    fun N₁ N₂ h => by simp [profiniteTransitionMap]⟩
  map_one' := by
    ext N
    simp [QuotientGroup.mk'_apply]
  map_mul' x y := by
    ext N
    simp [QuotientGroup.mk'_apply]

def IsStronglyComplete (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

noncomputable def abstractTransitionMap {G : Type*} [Group G]
    (N₁ N₂ : _root_.FiniteIndexNormalSubgroup G) (h : N₁ ≤ N₂) :
    G ⧸ (N₁ : Subgroup G) →* G ⧸ (N₂ : Subgroup G) := by
  haveI : (N₁ : Subgroup G).Normal := N₁.isNormal'
  haveI : (N₂ : Subgroup G).Normal := N₂.isNormal'
  exact QuotientGroup.map (N₁ : Subgroup G) (N₂ : Subgroup G) (MonoidHom.id G) (by simpa using h)

noncomputable def abstractProfiniteCompletionSubgroup (G : Type*) [Group G] :
    Subgroup ((N : _root_.FiniteIndexNormalSubgroup G) → G ⧸ (N : Subgroup G)) where
  carrier := { f | ∀ (N₁ N₂ : _root_.FiniteIndexNormalSubgroup G) (h : N₁ ≤ N₂),
    abstractTransitionMap N₁ N₂ h (f N₁) = f N₂ }
  mul_mem' := by
    intro a b ha hb N₁ N₂ h
    simp only [Pi.mul_apply, map_mul, ha N₁ N₂ h, hb N₁ N₂ h]
  one_mem' := by
    intro N₁ N₂ h
    simp only [Pi.one_apply, map_one]
  inv_mem' := by
    intro a ha N₁ N₂ h
    simp only [Pi.inv_apply, map_inv, ha N₁ N₂ h]

noncomputable def toAbstractProfiniteCompletion (G : Type*) [Group G] :
    G →* abstractProfiniteCompletionSubgroup G where
  toFun g := ⟨fun N => by
    haveI := N.isNormal'
    exact QuotientGroup.mk' _ g,
    fun N₁ N₂ h => by simp [abstractTransitionMap]⟩
  map_one' := by ext N; simp [QuotientGroup.mk'_apply]
  map_mul' x y := by ext N; simp [QuotientGroup.mk'_apply]

noncomputable def OpenNormalSubgroup.comapContinuousMulEquiv
    {G : Type*} {H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : OpenNormalSubgroup H) : OpenNormalSubgroup G where
  toOpenSubgroup := {
    toSubgroup := (N : Subgroup H).comap e.toMonoidHom
    isOpen' := by
      show IsOpen ((N : Subgroup H).comap e.toMonoidHom : Set G)
      rw [Subgroup.coe_comap]
      exact e.toHomeomorph.isOpen_preimage.mpr N.toOpenSubgroup.isOpen'
  }
  isNormal' := by
    show ((N : Subgroup H).comap e.toMonoidHom).Normal
    exact N.isNormal'.comap e.toMonoidHom

open CategoryTheory in
noncomputable def quotientMulEquivOfContinuousMulEquiv
    {G : Type*} {H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) (N : OpenNormalSubgroup H) :
    H ⧸ (N : Subgroup H) ≃*
      G ⧸ (OpenNormalSubgroup.comapContinuousMulEquiv e N : Subgroup G) := by
  haveI : ((N : Subgroup H).comap e.toMonoidHom).Normal := N.isNormal'.comap e.toMonoidHom
  haveI : (N : Subgroup H).Normal := N.isNormal'
  exact (QuotientGroup.congr _ _ e.toMulEquiv
    (Subgroup.map_comap_eq_self_of_surjective e.toMulEquiv.surjective _)).symm

noncomputable def galoisGroup_continuousMulEquiv_limit [IsGalois k K] :
    Gal(K/k) ≃ₜ*
      (ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor k K)).toProfinite.toTop :=
  InfiniteGalois.continuousMulEquivToLimit k K

noncomputable def absoluteGaloisGroup_profinite_iso
    (K₀ : Type*) [Field K₀] [CharZero K₀] :
    (AlgebraicClosure K₀ ≃ₐ[K₀] AlgebraicClosure K₀) ≃ₜ*
      (ProfiniteGrp.limit
        (InfiniteGalois.asProfiniteGaloisGroupFunctor K₀
          (AlgebraicClosure K₀))).toProfinite.toTop :=
  InfiniteGalois.continuousMulEquivToLimit K₀ (AlgebraicClosure K₀)

end ProfiniteGroups
end Ideles
end
