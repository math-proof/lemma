import Lemma.AlgebraicGeometry.ProjSpace
import Lemma.AlgebraicGeometry.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Notation.AlgebraicGeometry_ProjSpaceCover

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpaceCover

def stdCover : Scheme.OrderedAffineCover.{u} (Proj 𝒜) where
  ι := ULift.{u} (Fin (n + 1))
  U j := AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  isAffineOpen j := AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j.down)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j.down))
    one_pos
  iSup_eq_top := by
    have key : (⨆ j : ULift.{u} (Fin (n + 1)),
        AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down))
        = ⨆ j : Fin (n + 1), AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
      refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
      · exact le_iSup (fun j' : Fin (n + 1) => AlgebraicGeometry.Proj.basicOpen 𝒜 (X j')) j.down
      · exact le_iSup (fun j' : ULift.{u} (Fin (n + 1)) =>
          AlgebraicGeometry.Proj.basicOpen 𝒜 (X j'.down)) (ULift.up j)
    rw [key]
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 _
      (irrelevant_le_span_X R n)

theorem stdCover_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCover R n).U j = AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down) := rfl

end StdCover

section StdCoverPullback

variable {A : Type u} [CommRing A] {n : ℕ}
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

def stdCoverPullback : Scheme.OrderedAffineCover.{u} W :=
  let f := ι
  { ι := ULift.{u} (Fin (n + 1))
    U := fun j => f ⁻¹ᵁ ((stdCover A n).U j)
    isAffineOpen := fun j => ((stdCover A n).isAffineOpen j).preimage f
    iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top f (stdCover A n).iSup_eq_top }

theorem stdCoverPullback_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCoverPullback ι).U j = ι ⁻¹ᵁ (stdCover A n).U j := rfl

end StdCoverPullback

end ProjSpace

end AlgebraicGeometry

end
