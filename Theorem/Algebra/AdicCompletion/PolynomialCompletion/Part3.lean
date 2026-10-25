import Mathlib
import Def.Algebra.AdicCompletion.PolynomialCompletion.Part2
set_option autoImplicit false


namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

@[simp] theorem evalₐ_ofLevelwiseEquiv (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (ofLevelwiseEquiv I J e he x) = e n (evalₐ I n x) :=
  evalₐ_levelwiseHom I J e he n x

@[simp] theorem evalₐ_ofLevelwiseEquiv_symm (n : ℕ) (y : AdicCompletion J S) :
    evalₐ I n ((ofLevelwiseEquiv I J e he).symm y) = (e n).symm (evalₐ J n y) :=
  evalₐ_levelwiseHom J I (fun n => (e n).symm) (he_symm I J e he) n y

theorem ofLevelwiseEquiv_of (x : R) (y : S) (hxy : ∀ n, e n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ y) :
    ofLevelwiseEquiv I J e he (of I R x) = of J S y := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_ofLevelwiseEquiv, evalₐ_of, evalₐ_of, hxy]

end Levelwise

end AdicCompletion

namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

theorem pow_le_comap_maximalIdeal_pow (n : ℕ) :
    q ^ n ≤ ((maximalIdeal (Localization.AtPrime q)) ^ n).comap
      (algebraMap R (Localization.AtPrime q)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.le_comap_map

theorem comap_maximalIdeal_pow (n : ℕ) :
    ((maximalIdeal (Localization.AtPrime q)) ^ n).comap (algebraMap R (Localization.AtPrime q))
      = q ^ n := by
  rcases n with _ | n
  · simp
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  refine IsLocalization.under_map_of_isPrimary_disjoint q.primeCompl (Localization.AtPrime q)
    (Ideal.isPrimary_of_isMaximal_radical ?_) ?_
  · rw [Ideal.radical_pow _ n.succ_ne_zero, hq.isPrime.radical]
    exact hq
  · exact Set.disjoint_left.mpr fun x hx hx' => hx (Ideal.pow_le_self n.succ_ne_zero hx')

end Localization.AtPrime
