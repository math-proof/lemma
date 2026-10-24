import Mathlib

set_option autoImplicit false

universe w u

open CategoryTheory Opposite

namespace AlgebraicGeometry.AffineLimit

variable (R : Type u) [CommRing R]

noncomputable abbrev specOver (A : Type u) [CommRing A] [Algebra R A] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

noncomputable abbrev specOverOfSubalgebra {A : Type u} [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) :
    specOver R A ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom A₀.val.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

noncomputable abbrev specOverOfLE {A : Type u} [CommRing A] [Algebra R A] (A₀ A₁ : Subalgebra R A) (h : A₀ ≤ A₁) :
    specOver R A₁ ⟶ specOver R A₀ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl)

variable {R}

def IsLFPSurj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (x : G.obj (op (specOver R A))),
    ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (x₀ : G.obj (op (specOver R A₀))),
      G.map (specOverOfSubalgebra R A₀).op x₀ = x

def IsLFPInj (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
    (x₀ x₀' : G.obj (op (specOver R A₀))),
    G.map (specOverOfSubalgebra R A₀).op x₀ = G.map (specOverOfSubalgebra R A₀).op x₀' →
    ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
      G.map (specOverOfLE R A₀ A₁ h).op x₀ = G.map (specOverOfLE R A₀ A₁ h).op x₀'

def HomIsLFP {X : Scheme.{u}} (ξ : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  (∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) ∧
  (∀ (A : Type u) [CommRing A] [Algebra R A] (A₀ : Subalgebra R A) (_ : A₀.FG)
      (φ₀ φ₀' : Spec (CommRingCat.of A₀) ⟶ X),
      φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      φ₀' ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A₀)) →
      Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀' →
      ∃ (A₁ : Subalgebra R A) (_ : A₁.FG) (h : A₀ ≤ A₁),
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀ =
          Spec.map (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom) ≫ φ₀')

end AlgebraicGeometry.AffineLimit
