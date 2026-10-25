import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part4
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

noncomputable def mapAlgEquiv (e : R ≃ₐ[k] S) (he : I.map (e : R →ₐ[k] S) ≤ J)
    (he' : J.map (e.symm : S →ₐ[k] R) ≤ I) :
    AdicCompletion I R ≃ₐ[k] AdicCompletion J S :=
  AlgEquiv.ofAlgHom (mapₐ I J (e : R →ₐ[k] S) he) (mapₐ J I (e.symm : S →ₐ[k] R) he')
    (AlgHom.ext fun y => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ J n y)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (J ^ n) (e (e.symm z)) = Ideal.Quotient.mk (J ^ n) z
      rw [AlgEquiv.apply_symm_apply])
    (AlgHom.ext fun x => ext_evalₐ fun n => by
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      rw [AlgHom.comp_apply, AlgHom.id_apply, evalₐ_mapₐ, evalₐ_mapₐ, ← hz]
      show Ideal.Quotient.mk (I ^ n) (e.symm (e z)) = Ideal.Quotient.mk (I ^ n) z
      rw [AlgEquiv.symm_apply_apply])

end Equiv
end AdicCompletion
