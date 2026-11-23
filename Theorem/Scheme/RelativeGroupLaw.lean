module

public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Structure.AlgebraicGeometry_RelativeGroupLaw

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory Scheme
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace NeronModelInfra


@[simp]
public theorem schemeHomOverToOverHom_left {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : (schemeHomOverToOverHom φ).left = φ.1 :=
  rfl


@[simp]
public theorem overHomToSchemeHomOver_coe {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) : (overHomToSchemeHomOver h).1 = h.left :=
  rfl


@[simp]
public theorem overHomToSchemeHomOver_schemeHomOverToOverHom {B Y X : Scheme.{u}} {g : Y ⟶ B}
    {f : X ⟶ B} (φ : SchemeHomOver g f) :
    overHomToSchemeHomOver (schemeHomOverToOverHom φ) = φ :=
  Subtype.ext (by simp)


@[simp]
public theorem schemeHomOverToOverHom_overHomToSchemeHomOver {B Y X : Scheme.{u}} {g : Y ⟶ B}
    {f : X ⟶ B} (h : Over.mk g ⟶ Over.mk f) :
    schemeHomOverToOverHom (overHomToSchemeHomOver h) = h :=
  Over.OverMorphism.ext (by simp)


@[simp]
public theorem schemeHomOverEquivOverHom_apply {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (φ : SchemeHomOver g f) : schemeHomOverEquivOverHom g f φ = schemeHomOverToOverHom φ :=
  rfl


@[simp]
public theorem schemeHomOverEquivOverHom_symm_apply {B Y X : Scheme.{u}} {g : Y ⟶ B} {f : X ⟶ B}
    (h : Over.mk g ⟶ Over.mk f) :
    (schemeHomOverEquivOverHom g f).symm h = overHomToSchemeHomOver h :=
  rfl

end NeronModelInfra

namespace GoodReductionJacobian


public theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl


namespace RelativeGroupLaw


public theorem IsCommutative.mul_comm {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {G : RelativeGroupLaw R f} (hc : G.IsCommutative)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x :=
  hc t x y


public theorem mul_inv_cancel {R : Type u} [CommRing R] {A : Scheme.{u}}
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


public theorem one_natural {R : Type u} [CommRing R] {A : Scheme.{u}}
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


public theorem relativeGroupLaw_pointwise_eq_of_isIso {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (G G' : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    G.mul t x y = G'.mul t x y ∧ G.one t = G'.one t ∧ G.inv t x = G'.inv t x :=
  ⟨(subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _,
    (subsingleton_schemeHomOver_of_isIso t f).allEq _ _⟩

end GoodReductionJacobian
