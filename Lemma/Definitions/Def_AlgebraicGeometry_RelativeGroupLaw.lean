import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace NeronModelInfra

def schemeHomOverToOverHom {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : Over.mk g ⟶ Over.mk f :=
  Over.homMk φ.1 (by simpa using φ.2)

@[simp]
theorem schemeHomOverToOverHom_left {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : (schemeHomOverToOverHom φ).left = φ.1 :=
  rfl

def overHomToSchemeHomOver {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : SchemeHomOver g f :=
  ⟨h.left, by simpa using Over.w h⟩

@[simp]
theorem overHomToSchemeHomOver_coe {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : (overHomToSchemeHomOver h).1 = h.left :=
  rfl

@[simp]
theorem overHomToSchemeHomOver_schemeHomOverToOverHom {B Y X : Scheme.{u}} {g : Y ⟶ B}
    {f : X ⟶ B} (φ : SchemeHomOver g f) :
    overHomToSchemeHomOver (schemeHomOverToOverHom φ) = φ :=
  Subtype.ext (by simp)

@[simp]
theorem schemeHomOverToOverHom_overHomToSchemeHomOver {B Y X : Scheme.{u}} {g : Y ⟶ B}
    {f : X ⟶ B} (h : Over.mk g ⟶ Over.mk f) :
    schemeHomOverToOverHom (overHomToSchemeHomOver h) = h :=
  Over.OverMorphism.ext (by simp)

def schemeHomOverEquivOverHom {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :
    SchemeHomOver g f ≃ (Over.mk g ⟶ Over.mk f) where
  toFun := schemeHomOverToOverHom
  invFun := overHomToSchemeHomOver
  left_inv := overHomToSchemeHomOver_schemeHomOverToOverHom
  right_inv := schemeHomOverToOverHom_overHomToSchemeHomOver

@[simp]
theorem schemeHomOverEquivOverHom_apply {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : schemeHomOverEquivOverHom g f φ = schemeHomOverToOverHom φ :=
  rfl

@[simp]
theorem schemeHomOverEquivOverHom_symm_apply {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) :
    (schemeHomOverEquivOverHom g f).symm h = overHomToSchemeHomOver h :=
  rfl

end NeronModelInfra

namespace GoodReductionJacobian

def schemeHomOverComp {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) : SchemeHomOver t' f :=
  ⟨ψ ≫ x.1, by rw [Category.assoc, x.2, hψ]⟩

@[simp]
theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl

structure RelativeGroupLaw (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) where

  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f → SchemeHomOver t f

  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), SchemeHomOver t f

  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    SchemeHomOver t f → SchemeHomOver t f

  mul_assoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y z : SchemeHomOver t f), mul t (mul t x y) z = mul t x (mul t y z)

  one_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t (one t) x = x

  mul_one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
    mul t x (one t) = x

  inv_mul_cancel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f), mul t (inv t x) x = one t

  mul_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f),
    schemeHomOverComp ψ hψ (mul t x y) =
      mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y)

namespace RelativeGroupLaw

def IsCommutative {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x

theorem IsCommutative.mul_comm {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x :=
  hc t x y

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

theorem mul_inv_cancel {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  calc G.mul t x (G.inv t x)
      = G.mul t (G.one t) (G.mul t x (G.inv t x)) := (G.one_mul t _).symm
    _ = G.mul t (G.mul t (G.inv t (G.inv t x)) (G.inv t x)) (G.mul t x (G.inv t x)) := by
        rw [G.inv_mul_cancel t (G.inv t x)]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.inv t x) (G.mul t x (G.inv t x))) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.mul t (G.inv t x) x) (G.inv t x)) := by
        rw [G.mul_assoc]
    _ = G.mul t (G.inv t (G.inv t x)) (G.mul t (G.one t) (G.inv t x)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t (G.inv t (G.inv t x)) (G.inv t x) := by rw [G.one_mul]
    _ = G.one t := G.inv_mul_cancel t (G.inv t x)

theorem one_natural {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _

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

theorem relativeGroupLaw_pointwise_eq_of_isIso {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (G G' : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    G.mul t x y = G'.mul t x y ∧ G.one t = G'.one t ∧ G.inv t x = G'.inv t x :=
  ⟨(subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _⟩

end GoodReductionJacobian
