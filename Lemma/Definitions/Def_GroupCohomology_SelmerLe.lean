import Lemma.Definitions.Def_GroupCohomology_Selmer

set_option autoImplicit false

universe u

open CategoryTheory Module

namespace groupCohomology

variable {k : Type u} [Field k]
variable {Γ : Type u} [Group Γ]
variable {ι : Type u} [Fintype ι] {Γv : ι → Type u} [∀ v, Group (Γv v)]
variable (loc : ∀ v, Γv v →* Γ) (M : Rep k Γ) (M' : Rep k Γ)
variable (pairing : ∀ v, H1 (Rep.res (loc v) M) →ₗ[k] H1 (Rep.res (loc v) M') →ₗ[k] k)

def greenbergWilesLe (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  finrank k (selmer loc M L)
      + finrank k M'.ρ.invariants
      + ∑ v, finrank k (Rep.res (loc v) M).ρ.invariants
    ≤ finrank k (selmer loc M' (dualConditions loc M M' pairing L))
      + finrank k M.ρ.invariants
      + ∑ v, finrank k (L v)

theorem greenbergWilesLe_of_greenbergWilesEq
    {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : greenbergWilesEq loc M M' pairing L) : greenbergWilesLe loc M M' pairing L :=
  le_of_eq h

structure IsGreenbergWilesLeDatum (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    Prop where

  finite_selmer : FiniteDimensional k (selmer loc M L)

  finite_dualSelmer :
    FiniteDimensional k (selmer loc M' (dualConditions loc M M' pairing L))

  finite_local : ∀ v, FiniteDimensional k (L v)

  le : greenbergWilesLe loc M M' pairing L

theorem IsGreenbergWilesDatum.toLe {L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))}
    (h : IsGreenbergWilesDatum loc M M' pairing L) :
    IsGreenbergWilesLeDatum loc M M' pairing L where
  finite_selmer := h.finite_selmer
  finite_dualSelmer := h.finite_dualSelmer
  finite_local := h.finite_local
  le := greenbergWilesLe_of_greenbergWilesEq loc M M' pairing h.formula

def selmerComparisonStep (L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  (∀ v, L v ≤ L' v) →
    finrank k (selmer loc M L')
        + finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + ∑ v, finrank k (L v)
      ≤ finrank k (selmer loc M L)
          + finrank k (selmer loc M' (dualConditions loc M M' pairing L'))
          + ∑ v, finrank k (L' v)

theorem selmerComparisonStep_refl (L : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) :
    selmerComparisonStep loc M M' pairing L L := fun _ => le_refl _

end groupCohomology
