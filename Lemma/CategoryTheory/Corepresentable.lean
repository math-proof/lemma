import Mathlib
import Def.Mathlib_CategoryTheory_Corepresentable

universe w v u

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} [Category.{v} C]

section Corepresentable

variable {F : C ⥤ Type w}


lemma isCorepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsCorepresentable :=
  (corepresentableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isCorepresentable

lemma isCorepresentable_iff_hasInitial_elements :
    F.IsCorepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isCorepresentable_of_hasInitial_elements⟩

end Corepresentable

section Representable

variable {F : Cᵒᵖ ⥤ Type w}


lemma isRepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsRepresentable :=
  (representableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isRepresentable

lemma isRepresentable_iff_hasInitial_elements :
    F.IsRepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isRepresentable_of_hasInitial_elements⟩

end Representable

end CategoryTheory.Functor
