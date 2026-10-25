import Mathlib

set_option autoImplicit false

noncomputable section

universe u v

open IsLocalRing

namespace FaithfullyFlatRegularDescent


section Carrier

def RegularDescendsAlongFaithfullyFlat : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] [IsRegularLocalRing B], IsRegularLocalRing A

def RegularDescendsAlongFlatLocalHom : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra A B] [Module.Flat A B] [IsRegularLocalRing B],
    IsLocalHom (algebraMap A B) → IsRegularLocalRing A

end Carrier

end FaithfullyFlatRegularDescent

end
