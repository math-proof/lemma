import Mathlib
import Abbrev.Algebra.AffineDilatation
set_option autoImplicit false


noncomputable section

universe u

namespace AffineDilatation

variable {A : Type u} [CommRing A]

noncomputable def divElem (I : Ideal A) (a : A) (g : A) (hg : g ∈ I) : Ring I a :=
  ⟨IsLocalization.mk' (Localization.Away a) g (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a),
    Algebra.subset_adjoin ⟨g, hg, rfl⟩⟩

end AffineDilatation
end
