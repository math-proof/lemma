import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part6
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

variable (f : R →ₐ[k] S)

noncomputable def mapAlgEquivOfBijective (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    AdicCompletion I R ≃ₐ[k] AdicCompletion J S :=
  AlgEquiv.ofRingEquiv
    (f := ofLevelwiseEquiv I J (levelEquiv I J f h hb) (factorPow_levelEquiv I J f h hb))
    (fun c => by
      rw [algebraMap_apply, algebraMap_apply]
      refine ofLevelwiseEquiv_of I J _ _ _ _ fun n => ?_
      rw [levelEquiv_apply, levelMapₐ_mk, AlgHom.commutes])

end Equiv
end AdicCompletion
