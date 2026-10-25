import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality.Part2
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Map

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

theorem mapₐAux_apply (h : I.map f ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    mapₐAux I J f h n x = levelMapₐ I J f h n (evalₐ I n x) :=
  rfl

theorem factorₐ_comp_mapₐAux (h : I.map f ≤ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hle)).comp (mapₐAux I J f h n)
      = mapₐAux I J f h m := by
  ext x
  show Ideal.Quotient.factorPow J hle (levelMapₐ I J f h n (evalₐ I n x))
    = levelMapₐ I J f h m (evalₐ I m x)
  rw [factorPow_levelMapₐ, factorPow_evalₐ]

end Map
end AdicCompletion
