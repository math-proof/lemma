import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Lemma.AlgebraicGeometry.TwoAffineOpenCover

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.RelPicard.LFP

open Scheme.TwoAffineOpenCover

variable (R : Type u) [CommRing R]

noncomputable def stageHom {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (f : A₀ →ₐ[R] A') : SchemeHomOver (specMap R A') (specMap R A₀) :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    change f.toRingHom (algebraMap R A₀ x) = algebraMap R A' x
    exact f.commutes x⟩

end AlgebraicGeometry.RelPicard.LFP
