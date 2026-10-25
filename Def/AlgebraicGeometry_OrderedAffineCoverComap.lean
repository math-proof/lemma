import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover


section Comap

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (f : Y ⟶ X) [IsAffineHom f]

def comap : Y.OrderedAffineCover where
  ι := 𝒰.ι
  instFintype := 𝒰.instFintype
  instLinearOrder := 𝒰.instLinearOrder
  U i := f ⁻¹ᵁ 𝒰.U i
  isAffineOpen i := (𝒰.isAffineOpen i).preimage f
  iSup_eq_top := by rw [← Scheme.Hom.preimage_iSup, 𝒰.iSup_eq_top]; rfl

end Comap

end AlgebraicGeometry.Scheme.OrderedAffineCover

end
