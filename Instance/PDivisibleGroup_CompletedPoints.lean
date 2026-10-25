-- Carved from Lemma/Definitions/Def_PDivisibleGroup_CompletedPoints.lean: instance decls only.
import Mathlib
import Instance.PDivisibleGroup_Points
import Lemma.PDivisibleGroup.CompletedPoints

set_option autoImplicit false

noncomputable section

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}


variable (G : PDivisibleGroup R p h) (S : Type) [CommRing S] [Algebra R S]


instance CPoints.instDistribMulAction : DistribMulAction (S ≃ₐ[R] S) (G.CPoints S) where
  smul σ x := G.cpointsMap (σ : S →ₐ[R] S) x
  one_smul x := by
    change G.cpointsMap ((1 : S ≃ₐ[R] S) : S →ₐ[R] S) x = x
    rw [show ((1 : S ≃ₐ[R] S) : S →ₐ[R] S) = AlgHom.id R S from rfl, cpointsMap_id]
    rfl
  mul_smul σ τ x := by
    change G.cpointsMap ((σ * τ : S ≃ₐ[R] S) : S →ₐ[R] S) x =
      G.cpointsMap (σ : S →ₐ[R] S) (G.cpointsMap (τ : S →ₐ[R] S) x)
    rw [show ((σ * τ : S ≃ₐ[R] S) : S →ₐ[R] S) = (σ : S →ₐ[R] S).comp (τ : S →ₐ[R] S) from rfl,
      cpointsMap_comp]
    rfl
  smul_zero σ := map_zero (G.cpointsMap (σ : S →ₐ[R] S))
  smul_add σ x y := map_add (G.cpointsMap (σ : S →ₐ[R] S)) x y

end PDivisibleGroup

end
