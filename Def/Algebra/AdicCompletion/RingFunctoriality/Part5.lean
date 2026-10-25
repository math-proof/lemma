import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part5
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

variable (f : R →ₐ[k] S)

noncomputable def levelEquiv (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n))
    (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ J ^ n :=
  RingEquiv.ofBijective (levelMapₐ I J f h n) (hb n)

end Equiv
end AdicCompletion
