import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality.Part4
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

@[simp]
theorem mapAlgEquiv_apply (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) (x : AdicCompletion I R) :
    mapAlgEquiv I J e he he' x = mapₐ I J (e : R →ₐ[k] S) he x :=
  rfl

@[simp]
theorem mapAlgEquiv_symm_apply (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) (y : AdicCompletion J S) :
    (mapAlgEquiv I J e he he').symm y = mapₐ J I (e.symm : S →ₐ[k] R) he' y :=
  rfl

end Equiv
end AdicCompletion
