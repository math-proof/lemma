-- Carved from Lemma/Definitions/Def_PDivisibleGroup_Points.lean: instance decls only.
import Mathlib
import Instance.PDivisibleGroup_Basic
import Instance.EllipticCurve_TateModule
import Lemma.PDivisibleGroup.Points

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv


namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
variable (L : Type) [CommRing L] [Algebra R L]

namespace Point

variable {G L} {v : ℕ}

instance instCommMonoid : CommMonoid (G.Point L v) :=
  inferInstanceAs (CommMonoid (WithConv (G.level v →ₐ[R] L)))

noncomputable instance instCommGroup : CommGroup (G.Point L v) := commGroupOfIsUnit isUnit

end Point

variable {L}

variable (L)

variable {L}

instance pointsDirectedSystem :
    DirectedSystem (fun v => Additive (G.Point L v)) fun v w hvw => G.pointsDirectedSystemMap (L := L) v w hvw where
  map_self _ x := G.pointInclLE_self _ x
  map_map _ _ _ huv hvw x := (G.pointInclLE_trans huv hvw x).symm

variable (L)

noncomputable instance Points.instAddCommGroup : AddCommGroup (G.Points L) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun v => Additive (G.Point L v)) fun v w hvw => G.pointsDirectedSystemMap v w hvw))

noncomputable instance Points.instInhabited : Inhabited (G.Points L) := ⟨0⟩

variable {L}


noncomputable instance Points.instDistribMulAction : DistribMulAction (L ≃ₐ[R] L) (G.Points L) where
  smul σ z := G.pointsMap (σ : L →ₐ[R] L) z
  one_smul z := by
    change G.pointsMap ((1 : L ≃ₐ[R] L) : L →ₐ[R] L) z = z
    rw [show ((1 : L ≃ₐ[R] L) : L →ₐ[R] L) = AlgHom.id R L from rfl, pointsMap_id]
    rfl
  mul_smul σ τ z := by
    change G.pointsMap ((σ * τ : L ≃ₐ[R] L) : L →ₐ[R] L) z =
      G.pointsMap (σ : L →ₐ[R] L) (G.pointsMap (τ : L →ₐ[R] L) z)
    rw [show ((σ * τ : L ≃ₐ[R] L) : L →ₐ[R] L) = (σ : L →ₐ[R] L).comp (τ : L →ₐ[R] L) from rfl,
      pointsMap_comp]
    rfl
  smul_zero σ := map_zero (G.pointsMap (σ : L →ₐ[R] L))
  smul_add σ z w := map_add (G.pointsMap (σ : L →ₐ[R] L)) z w


end PDivisibleGroup

end
