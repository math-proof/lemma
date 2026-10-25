import Mathlib
import Abbrev.GroupCohomology_TateCohomology
import Lemma.Representation.EqIndBotMk

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

abbrev indBotMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.indBot ⟶ B.indBot :=
  Rep.indMap (⊥ : Subgroup G).subtype ((Rep.resFunctor (⊥ : Subgroup G).subtype).map φ)

end Rep

end
