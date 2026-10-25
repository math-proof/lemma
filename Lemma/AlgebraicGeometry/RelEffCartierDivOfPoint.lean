import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Lemma.AlgebraicGeometry.RelEffCartierDiv
import Instance.AlgebraicGeometry_RelEffCartierDivOfPoint
import Def.AlgebraicGeometry_RelEffCartierDivOfPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) {T : Scheme.{u}} {g : T ⟶ S}


lemma graphOver_eq_lift (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha = pullback.lift a (𝟙 T) (ha.trans (Category.id_comp g).symm) := rfl

@[reassoc (attr := simp)]
lemma graphOver_fst (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.fst f g = a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphOver_snd (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    graphOver f a ha ≫ pullback.snd f g = 𝟙 T :=
  pullback.lift_snd _ _ _


@[simp] lemma RelEffCartierDiv.ofPoint_I [IsSeparated f] (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    (RelEffCartierDiv.ofPoint f a ha).I = (graphOver f a ha).ker := rfl


variable {f} in

@[reassoc (attr := simp)]
lemma RelEffCartierDiv.toPoint_comp (D : RelEffCartierDiv f 1 g) : D.toPoint ≫ f = g := by
  calc D.toPoint ≫ f
      = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ D.I.subschemeι ≫ (pullback.fst f g ≫ f) := by
        simp only [RelEffCartierDiv.toPoint, Category.assoc]
    _ = inv (D.I.subschemeι ≫ pullback.snd f g) ≫ (D.I.subschemeι ≫ pullback.snd f g) ≫ g := by
        rw [pullback.condition, Category.assoc]
    _ = g := by rw [IsIso.inv_hom_id_assoc]

end AlgebraicGeometry
