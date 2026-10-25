import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part2
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Map

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

noncomputable def mapₐAux (h : I.map f ≤ J) (n : ℕ) : AdicCompletion I R →ₐ[k] S ⧸ J ^ n :=
  (levelMapₐ I J f h n).comp ((evalₐ I n).restrictScalars k)

end Map
end AdicCompletion
