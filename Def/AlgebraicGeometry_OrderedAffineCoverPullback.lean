import Def.AlgebraicGeometry_OrderedAffineCoverComap
import Lemma.Scheme.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Abbrev.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

noncomputable section

universe u


namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover

section BaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

abbrev baseChange : (Limits.pullback π (specMap R A)).OrderedAffineCover :=
  haveI := isAffineHom_fst π A
  𝒰.comap (Limits.pullback.fst π (specMap R A))

end BaseChange

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

def pullback : (Limits.pullback π (specMap R A)).TwoAffineOpenCover :=
  haveI := isAffineHom_fst π A
  { U0 := (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒱.U0
    U1 := (Limits.pullback.fst π (specMap R A)) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
