import Mathlib

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology

section Carry

variable {G : Type} [Group G]

noncomputable def cyclicLog (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s) (g : G) : ℕ :=
  ((finEquivZPowers hfin).symm ⟨g, hs g⟩ : Fin (orderOf s))

noncomputable def carryFun (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    {A : Rep ℤ G} (a : A) : G × G → A :=
  fun p => if orderOf s ≤ cyclicLog s hs hfin p.1 + cyclicLog s hs hfin p.2 then a else 0

noncomputable def cyclicInv (s : G) {A : Rep ℤ G} (c : G × G → A) : A :=
  ∑ i ∈ Finset.range (orderOf s), c (s ^ i, s)

end Carry

end groupCohomology
