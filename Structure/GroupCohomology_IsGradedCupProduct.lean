import Mathlib
import Abbrev.GroupCohomology_CochainCup
import Abbrev.GroupCohomology_GradedCupFamily
import Def.GroupCohomology_CochainCup

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)


structure IsGradedCupProduct (cup : GradedCupFamily A B) : Prop where
  compat : ∀ (p q : ℕ) (x : cocycles A p) (y : cocycles B q)
    (h : (inhomogeneousCochains.d (A ⊗ B) (p + q)).hom
      (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) = 0),
    cup p q ((groupCohomology.π A p).hom x) ((groupCohomology.π B q).hom y)
      = (groupCohomology.π (A ⊗ B) (p + q)).hom
          (cocyclesMk (cochainCup A B p q ((iCocycles A p).hom x) ((iCocycles B q).hom y)) h)

end groupCohomology
