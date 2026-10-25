import Mathlib
import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
import Abbrev.CerednikDrinfeld_SchemeNilpPoints

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪]

theorem Scheme.specMap_algHom_comp_specOver {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B']
    [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B' := by
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_algebraMap]

def Scheme.nilpPoints {X : Scheme.{0}} (f : X ⟶ Spec (.of 𝒪)) : AlgFunctor 𝒪 where
  obj B _ _ := { φ : Spec (.of B) ⟶ X // φ ≫ f = Scheme.specOver B }
  map g φ := ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1, by
    rw [Category.assoc, φ.2, Scheme.specMap_algHom_comp_specOver]⟩
  map_id φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ φ.1 = φ.1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  map_comp g h φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom ((h.comp g).toRingHom)) ≫ φ.1 =
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1)
    simp only [AlgHom.toRingHom_eq_coe]
    rw [AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

@[simp] theorem Scheme.nilpPoints_map_val {X : Scheme.{0}} (f : X ⟶ Spec (.of 𝒪)) {B : Type} [CommRing B]
    [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') (φ : (Scheme.nilpPoints f).obj B) :
    ((Scheme.nilpPoints f).map g φ).1 = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1 := rfl

def Scheme.nilpPoints.mapHom {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of 𝒪)) (fY : Y ⟶ Spec (.of 𝒪)) (h : X ⟶ Y)
    (w : h ≫ fY = fX) : AlgFunctor.NatTrans (Scheme.nilpPoints fX) (Scheme.nilpPoints fY) where
  app B _ _ φ := ⟨φ.1 ≫ h, by rw [Category.assoc, w, φ.2]⟩
  naturality g φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (φ.1 ≫ h) = (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1) ≫ h
    rw [Category.assoc]

def Scheme.nilpPoints.specPoint (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (Scheme.nilpPoints (𝟙 (Spec (CommRingCat.of 𝒪)))).obj B :=
  ⟨Scheme.specOver B, Category.comp_id _⟩

end AlgebraicGeometry

end
