import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section LevelMap

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

def levelMapₐ (h : I.map f ≤ J) (n : ℕ) : R ⧸ I ^ n →ₐ[k] S ⧸ J ^ n :=
  Ideal.quotientMapₐ (J ^ n) f (pow_le_comap_pow I J f h n)

end LevelMap
end AdicCompletion
