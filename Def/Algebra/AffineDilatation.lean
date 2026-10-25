import Mathlib
set_option autoImplicit false


noncomputable section

universe u

namespace AffineDilatation

variable {A : Type u} [CommRing A]

def gen (I : Ideal A) (a : A) : Set (Localization.Away a) :=
  (fun g : A => IsLocalization.mk' (Localization.Away a) g
    (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)) '' (I : Set A)

def subalgebra (I : Ideal A) (a : A) : Subalgebra A (Localization.Away a) :=
  Algebra.adjoin A (gen I a)

end AffineDilatation
end
