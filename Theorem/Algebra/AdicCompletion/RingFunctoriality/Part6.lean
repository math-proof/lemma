import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality.Part5
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

variable (f : R →ₐ[k] S)

theorem levelEquiv_apply (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n))
    (n : ℕ) (x : R ⧸ I ^ n) :
    levelEquiv I J f h hb n x = levelMapₐ I J f h n x :=
  rfl

theorem factorPow_levelEquiv (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (levelEquiv I J f h hb n x)
      = levelEquiv I J f h hb m (Ideal.Quotient.factorPow I hmn x) :=
  factorPow_levelMapₐ I J f h hmn x

end Equiv
end AdicCompletion
