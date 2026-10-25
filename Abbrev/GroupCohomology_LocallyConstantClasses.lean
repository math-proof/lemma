import Mathlib

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

noncomputable abbrev inflation (M : Rep k G) (S : Subgroup G) [S.Normal] :
    H1 (M.quotientToInvariants S) ⟶ H1 M :=
  groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (M.ρ.quotientToInvariants_lift S)) 1

end groupCohomology
