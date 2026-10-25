import Mathlib

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

namespace SubalgebraStages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)

noncomputable abbrev specHom (i : ι) : Spec (CommRingCat.of ↥(S i)) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(S i)))

noncomputable abbrev specHomTop : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ A))

noncomputable abbrev specTrans {i j : ι} (h : i ≤ j) : Spec (CommRingCat.of ↥(S j)) ⟶ Spec (CommRingCat.of ↥(S i)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (S.mono h)).toRingHom)

noncomputable abbrev specLeg (i : ι) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥(S i)) :=
  Spec.map (CommRingCat.ofHom (S i).val.toRingHom)

noncomputable abbrev obj (i : ι) : Scheme.{u} := pullback f (specHom S i)


end SubalgebraStages

end AlgebraicGeometry
