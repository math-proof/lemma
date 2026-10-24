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

import sympy.atlas.v1.Atlas.NumberTheoryI.code.Adeles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles

noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

abbrev IdeleGroup := (NumberField.AdeleRing (𝓞 K) K)ˣ

def principalIdeleEmb : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom

def principalIdeles : Subgroup (IdeleGroup K) :=
  (principalIdeleEmb K).range

abbrev IdeleClassGroup := (IdeleGroup K) ⧸ (principalIdeles K)

instance ideleGroup_locallyCompact :
    LocallyCompactSpace (IdeleGroup K) :=
  inferInstance

lemma adeleRing_unit_fin_norm_finMulSupport (a : IdeleGroup K) :
    (Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖)).Finite := by
  have ha := (a : NumberField.AdeleRing (𝓞 K) K).2.2
  have hai := (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2.2
  rw [Filter.eventually_cofinite] at ha hai
  apply Set.Finite.subset (ha.union hai)
  intro v hv
  rw [Function.mem_mulSupport] at hv
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra h
  push Not at h
  obtain ⟨hv1, hv2⟩ := h
  have h1 : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv1
  have h2 : ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv2
  have hmul : (↑a : NumberField.AdeleRing (𝓞 K) K).2 v *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v = 1 := by
    change ((↑a : NumberField.AdeleRing (𝓞 K) K).2 *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2) v =
      (1 : NumberField.AdeleRing (𝓞 K) K).2 v
    congr 1; exact congr_arg Prod.snd (Units.mul_inv a)
  have hnm : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
      ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hge : 1 ≤ ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
    by_contra hlt; push Not at hlt
    linarith [mul_le_mul_of_nonneg_left h2
      (norm_nonneg ((a : NumberField.AdeleRing (𝓞 K) K).2 v))]
  exact hv (le_antisymm h1 hge)

def adelicNorm : IdeleGroup K →* ℝ where
  toFun a := NumberField.Adeles.adelicAbsVal (a : NumberField.AdeleRing (𝓞 K) K)
  map_one' := by
    show NumberField.Adeles.adelicAbsVal
      ((1 : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K) = 1
    rw [Units.val_one]
    unfold NumberField.Adeles.adelicAbsVal
    have h1 : ∀ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ = 1 := by
      intro w
      show ‖(1 : InfiniteAdeleRing K) w‖ = 1
      have : (1 : InfiniteAdeleRing K) w = 1 := Pi.one_apply w
      rw [this]; exact IsAbsoluteValue.abv_one' norm
    have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
      intro v
      show ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1
      have : (1 : FiniteAdeleRing (𝓞 K) K) v = 1 := RestrictedProduct.one_apply _ v
      rw [this, norm_one]
    have hinf : (∏ w : InfinitePlace K,
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) = 1 := by
      apply Finset.prod_eq_one; intro w _; rw [h1 w, one_pow]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) = 1 := by
      rw [show (fun v => ‖(1 : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (fun _ => (1 : ℝ)) from funext h2]
      exact finprod_one
    rw [hinf, hfin, mul_one]

  map_mul' a b := by
    show NumberField.Adeles.adelicAbsVal _ = NumberField.Adeles.adelicAbsVal _ *
      NumberField.Adeles.adelicAbsVal _
    unfold NumberField.Adeles.adelicAbsVal
    have hinf : (∏ w : InfinitePlace K,
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) =
        (∏ w, ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) *
        (∏ w, ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ ^ w.mult) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro w _
      have hmul : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w =
                  (a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).1 w = _; rfl
      rw [hmul]
      have hn : ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w *
                  (b : NumberField.AdeleRing (𝓞 K) K).1 w‖ =
                ‖(a : NumberField.AdeleRing (𝓞 K) K).1 w‖ *
                ‖(b : NumberField.AdeleRing (𝓞 K) K).1 w‖ :=
        NormedField.norm_mul _ _
      erw [hn, mul_pow]
    have hfmul : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖ =
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
        ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
      intro v
      have : ((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v =
             (a : NumberField.AdeleRing (𝓞 K) K).2 v *
             (b : NumberField.AdeleRing (𝓞 K) K).2 v := by
        show ((↑a * ↑b : NumberField.AdeleRing (𝓞 K) K)).2 v = _; rfl
      rw [this, norm_mul]
    have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        ‖((a * b : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 v‖) =
        (∏ᶠ v, ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖) *
        (∏ᶠ v, ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) := by
      rw [show (fun v => ‖((a * b : IdeleGroup K) :
            NumberField.AdeleRing (𝓞 K) K).2 v‖) =
          (fun v => ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
            ‖(b : NumberField.AdeleRing (𝓞 K) K).2 v‖) from funext hfmul]
      exact finprod_mul_distrib
        (adeleRing_unit_fin_norm_finMulSupport K a)
        (adeleRing_unit_fin_norm_finMulSupport K b)
    rw [hinf, hfin]; ring

def OneIdeleGroup : Subgroup (IdeleGroup K) :=
  (adelicNorm K).ker

abbrev NormOneIdeleClassGroup :=
    (OneIdeleGroup K) ⧸ (principalIdeles K).subgroupOf (OneIdeleGroup K)

end OneIdeles

section ProfiniteGroups

open CategoryTheory in
class IsProfiniteGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop where
  isInverseLimitOfFiniteGroups :
    ∃ (J : Type) (_ : SmallCategory J) (F : Functor J FiniteGrp.{0}),
      Nonempty (G ≃ₜ* ProfiniteGrp.limit (F ⋙ forget₂ FiniteGrp ProfiniteGrp))

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
