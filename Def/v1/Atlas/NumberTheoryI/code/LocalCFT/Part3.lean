/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.NumberTheoryI.code.LocalCFT.Part2
open scoped RestrictedProduct
open Filter Set


noncomputable section

open scoped Pointwise

attribute [instance] LocalArtinReciprocity.kx_comm_group
  LocalArtinReciprocity.kx_topological_space
  LocalArtinReciprocity.kx_topological_group
  LocalArtinReciprocity.ext_preorder
  LocalArtinReciprocity.gal_comm_group
  LocalArtinReciprocity.gal_fintype

namespace LocalArtinReciprocity

variable (D : LocalArtinReciprocity)

attribute [instance] LocalArtinMap.galAb_group
  LocalArtinMap.galAb_topological_space
  LocalArtinMap.galAb_topological_group
  LocalArtinMap.galAb_compact
  LocalArtinMap.gal_topological_space
  LocalArtinMap.gal_discrete_topology

namespace LocalArtinMap

variable (M : LocalArtinMap)

def ProfiniteCompletionKx : Subgroup (∀ i, M.Kx ⧸ M.normGroup i) where
  carrier := {x | ∀ ⦃i j : M.I⦄ (h : i ≤ j),
    QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
      (M.toLocalArtinReciprocity.normGroup_antitone h) (x j) = x i}
  one_mem' := fun i j h => by simp [map_one]
  mul_mem' := fun ha hb i j h => by simp [map_mul, ha h, hb h]
  inv_mem' := fun ha i j h => by simp [map_inv, ha h]

def InvLimGalLK : Subgroup (∀ i, M.GalLK i) where
  carrier := {x | ∀ ⦃i j : M.I⦄ (h : i ≤ j), M.restrictMap h (x j) = x i}
  one_mem' := fun i j h => by simp [map_one]
  mul_mem' := fun ha hb i j h => by simp [map_mul, ha h, hb h]
  inv_mem' := fun ha i j h => by simp [map_inv, ha h]

def profiniteCompletionIso : M.ProfiniteCompletionKx ≃* M.InvLimGalLK := by

  let fwd_i (i : M.I) : M.Kx ⧸ M.normGroup i →* M.GalLK i :=
    QuotientGroup.lift (M.normGroup i) (M.artinMap i) (by rw [M.artinMap_ker i])

  have fwd_mk : ∀ (i : M.I) (x : M.Kx),
      fwd_i i (QuotientGroup.mk x) = M.artinMap i x :=
    fun i x => QuotientGroup.lift_mk _ _ _

  have naturality : ∀ ⦃i j : M.I⦄ (h : i ≤ j) (x : M.Kx),
      M.restrictMap h (fwd_i j (QuotientGroup.mk x)) =
        fwd_i i (QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
          (M.toLocalArtinReciprocity.normGroup_antitone h) (QuotientGroup.mk x)) := by
    intro i j h x
    rw [fwd_mk, QuotientGroup.map_mk, MonoidHom.id_apply, fwd_mk]
    exact M.artinMap_compat h x

  let piHom : (∀ i, M.Kx ⧸ M.normGroup i) →* (∀ i, M.GalLK i) :=
    Pi.monoidHom fun i => (fwd_i i).comp (Pi.evalMonoidHom _ i)

  have piHom_maps : ∀ q ∈ M.ProfiniteCompletionKx,
      piHom q ∈ M.InvLimGalLK := by
    intro q hq i j h
    show M.restrictMap h (fwd_i j (q j)) = fwd_i i (q i)
    rw [← hq h]
    exact QuotientGroup.induction_on (q j) (fun x => naturality h x)

  have fwd_bij : ∀ i, Function.Bijective (fwd_i i) := fun i => by
    constructor
    ·
      intro a b hab
      obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hab
      rw [QuotientGroup.eq, ← M.artinMap_ker i]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hab, inv_mul_cancel])
    · intro σ
      obtain ⟨x, hx⟩ := M.artinMap_surjective i σ
      exact ⟨QuotientGroup.mk x, by rw [fwd_mk]; exact hx⟩

  let fwdSubHom : M.ProfiniteCompletionKx →* M.InvLimGalLK :=
    (piHom.comp M.ProfiniteCompletionKx.subtype).codRestrict M.InvLimGalLK
      (fun ⟨q, hq⟩ => piHom_maps q hq)

  refine MulEquiv.ofBijective fwdSubHom ⟨?_, ?_⟩
  ·
    intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ heq
    ext i
    have : fwd_i i (q₁ i) = fwd_i i (q₂ i) :=
      congr_arg (fun x => (x : ∀ i, M.GalLK i) i) (Subtype.ext_iff.mp heq)
    exact (fwd_bij i).1 this
  ·

    intro ⟨σ, hσ⟩
    choose q hq_eq using fun i => (fwd_bij i).2 (σ i)
    refine ⟨⟨q, fun i j h => ?_⟩, Subtype.ext (funext hq_eq)⟩


    apply (fwd_bij i).1


    have step1 : fwd_i i (QuotientGroup.map (M.normGroup j) (M.normGroup i) (MonoidHom.id M.Kx)
        (M.toLocalArtinReciprocity.normGroup_antitone h) (q j)) =
        M.restrictMap h (fwd_i j (q j)) :=
      QuotientGroup.induction_on (q j) fun x => by
        rw [fwd_mk, QuotientGroup.map_mk, MonoidHom.id_apply, fwd_mk]
        exact (M.artinMap_compat h x).symm
    rw [step1, hq_eq j, hq_eq i]
    exact hσ h

def galAbIso : M.GalAb ≃* M.InvLimGalLK := by

  let fwd : M.GalAb →* (i : M.I) → M.GalLK i :=
    Pi.monoidHom fun i => M.proj i
  have fwd_mem : ∀ g, fwd g ∈ M.InvLimGalLK :=
    fun g i j h => M.proj_compat h g
  let fwdSub : M.GalAb →* M.InvLimGalLK :=
    fwd.codRestrict M.InvLimGalLK fwd_mem
  refine MulEquiv.ofBijective fwdSub ⟨?inj, ?surj⟩
  case inj =>
    intro a b hab
    have h := Subtype.ext_iff.mp hab
    have : ∀ i, M.proj i (a * b⁻¹) = 1 := fun i => by
      have hi : (fwd a) i = (fwd b) i := congr_fun h i
      simp [fwd, Pi.monoidHom, MonoidHom.coe_mk] at hi
      rw [map_mul, map_inv, hi, mul_inv_cancel]
    have := M.proj_jointly_injective (a * b⁻¹) this
    rw [mul_inv_eq_one] at this
    exact this
  case surj =>
    intro ⟨σ, hσ⟩

    by_cases hI : IsEmpty M.I
    ·
      exact ⟨1, Subtype.ext (funext (fun i => hI.elim i))⟩
    ·
      rw [not_isEmpty_iff] at hI
      haveI : Nonempty M.I := hI


      let F : M.I → Set M.GalAb := fun i => {g | M.proj i g = σ i}

      have hne : ∀ i, (F i).Nonempty := fun i => by
        obtain ⟨x, hx⟩ := M.artinMap_surjective i (σ i)
        exact ⟨M.artinHom x, by simp [F, ← M.artinMap_eq_proj, hx]⟩

      have hcl : ∀ i, IsClosed (F i) := fun i => M.proj_fiber_isClosed i (σ i)

      have hcpt : ∀ i, IsCompact (F i) := fun i =>
        (hcl i).isCompact

      have hdir : Directed (· ⊇ ·) F := by
        intro i j
        obtain ⟨k, hki, hkj, _⟩ := M.toLocalArtinReciprocity.exists_sup i j
        refine ⟨k, fun g hg => ?_, fun g hg => ?_⟩
        · simp only [F, Set.mem_setOf_eq] at hg ⊢
          rw [← M.proj_compat hki g, hg, hσ hki]
        · simp only [F, Set.mem_setOf_eq] at hg ⊢
          rw [← M.proj_compat hkj g, hg, hσ hkj]

      have hint := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        F hdir hne hcpt hcl
      obtain ⟨g, hg⟩ := hint
      simp only [Set.mem_iInter, Set.mem_setOf_eq, F] at hg
      exact ⟨g, Subtype.ext (funext hg)⟩

def profiniteCompletionMulEquiv : M.ProfiniteCompletionKx ≃* M.GalAb :=
  M.profiniteCompletionIso.trans M.galAbIso.symm

end LocalArtinMap
end LocalArtinReciprocity
end
