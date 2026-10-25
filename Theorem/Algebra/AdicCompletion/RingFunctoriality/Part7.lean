import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality.Part6
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section Equiv

variable (I : Ideal R) (J : Ideal S)

variable (f : R →ₐ[k] S)

@[simp]
theorem mapAlgEquivOfBijective_apply (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : AdicCompletion I R) :
    mapAlgEquivOfBijective I J f h hb x = mapₐ I J f h x :=
  ext_evalₐ fun n => by
    show evalₐ J n (ofLevelwiseEquiv I J (levelEquiv I J f h hb)
      (factorPow_levelEquiv I J f h hb) x) = _
    rw [evalₐ_ofLevelwiseEquiv, evalₐ_mapₐ, levelEquiv_apply]

theorem coe_mapAlgEquivOfBijective (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    (mapAlgEquivOfBijective I J f h hb : AdicCompletion I R →ₐ[k] AdicCompletion J S)
      = mapₐ I J f h :=
  AlgHom.ext (mapAlgEquivOfBijective_apply I J f h hb)

theorem mapₐ_bijective (h : I.map f ≤ J) (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) :
    Function.Bijective (mapₐ I J f h) := by
  have hB := (mapAlgEquivOfBijective I J f h hb).bijective
  rwa [show ⇑(mapAlgEquivOfBijective I J f h hb) = ⇑(mapₐ I J f h) from
    funext (mapAlgEquivOfBijective_apply I J f h hb)] at hB

theorem mapAlgEquivOfBijective_of (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : R) :
    mapAlgEquivOfBijective I J f h hb (of I R x) = of J S (f x) := by
  rw [mapAlgEquivOfBijective_apply, mapₐ_of]

theorem levelMapₐ_evalₐ_mapAlgEquivOfBijective_symm (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (n : ℕ) (y : AdicCompletion J S) :
    levelMapₐ I J f h n (evalₐ I n ((mapAlgEquivOfBijective I J f h hb).symm y)) = evalₐ J n y := by
  conv_rhs => rw [← (mapAlgEquivOfBijective I J f h hb).apply_symm_apply y]
  rw [mapAlgEquivOfBijective_apply, evalₐ_mapₐ]

theorem mapAlgEquivOfBijective_symm_of (h : I.map f ≤ J)
    (hb : ∀ n, Function.Bijective (levelMapₐ I J f h n)) (x : R) :
    (mapAlgEquivOfBijective I J f h hb).symm (of J S (f x)) = of I R x := by
  rw [AlgEquiv.symm_apply_eq, mapAlgEquivOfBijective_of]

end Equiv
end AdicCompletion
