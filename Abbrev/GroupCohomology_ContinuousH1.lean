import Mathlib
import Lemma.GroupCohomology.ContinuousH2
import Lemma.GroupCohomology.ContinuousH2Map

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace groupCohomology

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

section carriers

variable (M : Rep k G)


end carriers

abbrev continuousH2MapHom {A B : Rep k G} (φ : A ⟶ B) : continuousH2 r A →ₗ[k] continuousH2 r B :=
  continuousH2Map (MonoidHom.id G) (fun _ => rfl) φ.hom.toLinearMap (fun g a => Rep.hom_comm_apply φ g a)

section delta

variable {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C)


end delta

end groupCohomology

end
