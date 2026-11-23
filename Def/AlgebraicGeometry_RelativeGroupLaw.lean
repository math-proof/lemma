module

public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Structure.AlgebraicGeometry_RelativeGroupLaw

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory Scheme
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace NeronModelInfra

def schemeHomOverToOverHom {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : Over.mk g ⟶ Over.mk f :=
  Over.homMk φ.1 (by simpa using φ.2)

def overHomToSchemeHomOver {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : SchemeHomOver g f :=
  ⟨h.left, by simpa using Over.w h⟩

def schemeHomOverEquivOverHom {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :
    SchemeHomOver g f ≃ (Over.mk g ⟶ Over.mk f) where
  toFun := schemeHomOverToOverHom
  invFun := overHomToSchemeHomOver
  left_inv := overHomToSchemeHomOver_schemeHomOverToOverHom
  right_inv := schemeHomOverToOverHom_overHomToSchemeHomOver

end NeronModelInfra

namespace GoodReductionJacobian

namespace RelativeGroupLaw

def IsCommutative {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x

@[reducible]
def pointGroup {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Group (SchemeHomOver t f) where
  mul x y := G.mul t x y
  one := G.one t
  inv x := G.inv t x
  mul_assoc := G.mul_assoc t
  one_mul := G.one_mul t
  mul_one := G.mul_one t
  inv_mul_cancel := G.inv_mul_cancel t

end RelativeGroupLaw

def trivialRelativeGroupLaw (R : Type u) [CommRing R] :
    RelativeGroupLaw R (𝟙 (Spec (CommRingCat.of R))) where
  mul := fun _ x _ => x
  one := fun t => ⟨t, Category.comp_id t⟩
  inv := fun _ x => x
  mul_assoc := fun _ _ _ _ => rfl
  one_mul := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (Spec (CommRingCat.of R)))).allEq _ _
  mul_one := fun _ _ => rfl
  inv_mul_cancel := fun t _ =>
    (subsingleton_schemeHomOver_of_isIso t (𝟙 (Spec (CommRingCat.of R)))).allEq _ _
  mul_natural := fun _ _ _ _ _ _ => rfl

end GoodReductionJacobian

end

end
