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

end AlgebraicGeometry.AffineLimit
