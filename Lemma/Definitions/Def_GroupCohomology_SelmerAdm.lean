import Mathlib
import Lemma.Definitions.Def_GroupCohomology_SelmerLe

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ)

noncomputable def selmerAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : Submodule k (H1 M) :=
  selmer loc M L ⊓ adm

lemma mem_selmerAdm_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (x : H1 M) :
    x ∈ selmerAdm loc M L adm ↔ (∀ v, (locRes loc M v).hom x ∈ L v) ∧ x ∈ adm := by
  rw [selmerAdm, Submodule.mem_inf, mem_selmer_iff]

lemma selmerAdm_le_selmer (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : selmerAdm loc M L adm ≤ selmer loc M L :=
  inf_le_left

lemma selmerAdm_le_adm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) : selmerAdm loc M L adm ≤ adm :=
  inf_le_right

@[simp]
lemma selmerAdm_top (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerAdm loc M L ⊤ = selmer loc M L :=
  inf_top_eq _

@[simp]
lemma selmerAdm_bot (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerAdm loc M L ⊥ = ⊥ :=
  inf_bot_eq _

instance finiteDimensional_selmerAdm_of_adm
    (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) (adm : Submodule k (H1 M))
    [FiniteDimensional k adm] : FiniteDimensional k (selmerAdm loc M L adm) :=
  Submodule.finiteDimensional_inf_right _ _

variable [Fintype ι] (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def greenbergWilesLeAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop :=
  finrank k (selmerAdm loc M L adm)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    ≤ finrank k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

theorem greenbergWilesLeAdm_top_iff (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    greenbergWilesLeAdm loc M M' pairing L ⊤ ⊤ ↔ greenbergWilesLe loc M M' pairing L := by
  unfold greenbergWilesLeAdm greenbergWilesLe
  rw [selmerAdm_top, selmerAdm_top]

structure IsGreenbergWilesLeDatumAdm (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M)))
    (adm : Submodule k (H1 M)) (adm' : Submodule k (H1 M')) : Prop where

  finite_selmer : FiniteDimensional k (selmerAdm loc M L adm)

  finite_dualSelmer :
    FiniteDimensional k (selmerAdm loc M' (dualConditions loc M M' pairing L) adm')

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLeAdm loc M M' pairing L adm adm'

theorem IsGreenbergWilesLeDatum.toAdm {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesLeDatum loc M M' pairing L) :
    IsGreenbergWilesLeDatumAdm loc M M' pairing L ⊤ ⊤ where
  finite_selmer := by rw [selmerAdm_top]; exact h.finite_selmer
  finite_dualSelmer := by rw [selmerAdm_top]; exact h.finite_dualSelmer
  finite_local := h.finite_local
  le := (greenbergWilesLeAdm_top_iff loc M M' pairing L).mpr h.le

end groupCohomology
