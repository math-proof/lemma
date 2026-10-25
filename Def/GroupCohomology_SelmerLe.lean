import Lemma.GroupCohomology.Selmer

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


def selmerComparisonStep (L L' : ∀ v, Submodule k (H1 (Rep.res (loc v) M))) : Prop :=
  (∀ v, L v ≤ L' v) →
    finrank k (selmer loc M L')
        + finrank k (selmer loc M' (dualConditions loc M M' pairing L))
        + ∑ v, finrank k (L v)
      ≤ finrank k (selmer loc M L)
          + finrank k (selmer loc M' (dualConditions loc M M' pairing L'))
          + ∑ v, finrank k (L' v)

end groupCohomology
