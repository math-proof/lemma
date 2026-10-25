-- Carved from Lemma/Definitions/Def_GoodReductionJacobian_RelativeGroupLawAlgPointsV2.lean: instance decls only.
import Mathlib
import Lemma.GoodReductionJacobian.RelativeGroupLawKernel
import Instance.AlgebraicGeometry_RelativeGroupLawEndDegree
import Lemma.GoodReductionJacobian.RelativeGroupLawAlgPointsV2

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

namespace AlgPoints

variable {L : RelativeGroupLaw R f} {hc : L.IsCommutative}
variable {T : Type} [CommRing T] [Algebra R T]

instance instAddCommGroup : AddCommGroup (L.AlgPoints hc T) :=
  @Additive.addCommGroup _ (L.pointCommGroup hc (Spec.map (CommRingCat.ofHom (algebraMap R T))))

instance instInhabited : Inhabited (L.AlgPoints hc T) := ⟨0⟩


instance instDistribMulAction : DistribMulAction (T ≃ₐ[R] T) (L.AlgPoints hc T) where
  smul σ x := map (σ : T →ₐ[R] T) x
  one_smul x := by
    change map ((1 : T ≃ₐ[R] T) : T →ₐ[R] T) x = x
    rw [show ((1 : T ≃ₐ[R] T) : T →ₐ[R] T) = AlgHom.id R T from rfl, map_id]
    rfl
  mul_smul σ τ x := by
    change map ((σ * τ : T ≃ₐ[R] T) : T →ₐ[R] T) x = map (σ : T →ₐ[R] T) (map (τ : T →ₐ[R] T) x)
    rw [show ((σ * τ : T ≃ₐ[R] T) : T →ₐ[R] T) = (σ : T →ₐ[R] T).comp (τ : T →ₐ[R] T) from rfl,
      map_comp]
    rfl
  smul_zero σ := map_zero _
  smul_add σ x y := map_add _ x y

end AlgPoints

end RelativeGroupLaw
end GoodReductionJacobian

end
