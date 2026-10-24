import Mathlib

universe w v u

namespace CategoryTheory.Functor

open Limits

variable {C : Type u} [Category.{v} C]

section Corepresentable

variable {F : C ⥤ Type w}

@[simps]
def corepresentableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.CorepresentableBy e.obj where
  homEquiv {Y} :=
    { toFun f := F.map f e.val
      invFun y := (he.to (F.elementsMk Y y)).hom
      left_inv f := congrArg Elements.Hom.hom
        (he.hom_ext (he.to (F.elementsMk Y (F.map f e.val))) ⟨f, rfl⟩)
      right_inv y := (he.to (F.elementsMk Y y)).map_val }
  homEquiv_comp {Y Y'} g f := by simp [FunctorToTypes.map_comp_apply]

lemma isCorepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsCorepresentable :=
  (corepresentableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isCorepresentable

lemma isCorepresentable_iff_hasInitial_elements :
    F.IsCorepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isCorepresentable_of_hasInitial_elements⟩

end Corepresentable

section Representable

variable {F : Cᵒᵖ ⥤ Type w}

@[simps]
def representableByOfIsInitial (e : F.Elements) (he : IsInitial e) :
    F.RepresentableBy e.obj.unop where
  homEquiv {Y} :=
    { toFun f := F.map f.op e.val
      invFun y := (he.to (F.elementsMk (Opposite.op Y) y)).hom.unop
      left_inv f := congrArg (fun g => Quiver.Hom.unop g.hom)
        (he.hom_ext (he.to (F.elementsMk (Opposite.op Y) (F.map f.op e.val))) ⟨f.op, rfl⟩)
      right_inv y := (he.to (F.elementsMk (Opposite.op Y) y)).map_val }
  homEquiv_comp {Y Y'} g f := by simp [FunctorToTypes.map_comp_apply]

lemma isRepresentable_of_hasInitial_elements [HasInitial F.Elements] :
    F.IsRepresentable :=
  (representableByOfIsInitial (⊥_ F.Elements) initialIsInitial).isRepresentable

lemma isRepresentable_iff_hasInitial_elements :
    F.IsRepresentable ↔ HasInitial F.Elements :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ isRepresentable_of_hasInitial_elements⟩

end Representable

end CategoryTheory.Functor
