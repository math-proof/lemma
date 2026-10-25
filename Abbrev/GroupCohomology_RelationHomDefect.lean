import Mathlib
import Instance.GroupCohomology_RelationModule
import Lemma.GroupCohomology.RelationModuleRes
import Abbrev.GroupCohomology_RepCokernel
import Abbrev.GroupCohomology_RepImage
import Lemma.GroupCohomology.RelationHomDefect

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]


end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)


abbrev defectQ : Rep ℤ G := GroupCohomology.RepImage.obj (preι B E)

abbrev defectX : Rep ℤ G := GroupCohomology.RepCokernel.obj (preι B E)


abbrev homSeq₂ : ShortComplex (Rep ℤ G) := GroupCohomology.RepImage.seq (preι B E)

end Int

section Infl

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

abbrev extInflR : Rep.res π ((ihom (Rep.relationModuleInt B)).obj E) ⟶ (ihom (Rep.relationModuleInt (Rep.res π B))).obj E' :=
  Rep.resIhom π (Rep.relationModuleInt B) E ≫ Rep.preHom (Rep.relationModuleInt.resMap π B) (Rep.res π E) ≫
    (ihom (Rep.relationModuleInt (Rep.res π B))).map φ

abbrev extInflF : Rep.res π ((ihom (Rep.free ℤ G B)).obj E) ⟶ (ihom (Rep.free ℤ G' (Rep.res π B))).obj E' :=
  Rep.resIhom π (Rep.free ℤ G B) E ≫ Rep.preHom (Rep.freeResMap π B) (Rep.res π E) ≫ (ihom (Rep.free ℤ G' (Rep.res π B))).map φ

end Infl

end Rep

end
