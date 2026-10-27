import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part7
open IsDedekindDomain LocallyFactorialDivisors
open scoped nonZeroDivisors


namespace LocallyFactorialDivisors

/--
[dedekind_isLocallyFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
lemma dedekind_isLocallyFactorial
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R] :
-- imply
  IsLocallyFactorial R := by
-- proof
  intro P hP
  by_cases hbot : P = ⊥
  ·
    subst hbot
    haveI : Ideal.IsPrime (⊥ : Ideal R) := hP
    exact inferInstance
  ·
    haveI := hP
    haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hbot _
    exact inferInstance
/-- If every localization at a prime is a regular local ring, then `R` is
locally factorial (Auslander–Buchsbaum). -/

end LocallyFactorialDivisors

namespace LocallyFactorialDivisors

/--
[cartierToWeil_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
lemma cartierToWeil_inv
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {u : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  cartierToWeil K u⁻¹ = -(cartierToWeil K u) := by
-- proof
  ext v
  simp only [cartierToWeil_apply, Finsupp.neg_apply, Units.val_inv_eq_inv_val]
  exact FractionalIdeal.count_inv K v (u : FractionalIdeal R⁰ K)

end LocallyFactorialDivisors

namespace LocallyFactorialDivisors

/--
[weil_eq_cartier_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
lemma weil_eq_cartier_dedekind
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  Function.Bijective (cartierToWeil (R := R) K) :=
-- proof
  ⟨cartierToWeil_injective K, cartierToWeil_surjective K⟩

end LocallyFactorialDivisors

namespace LocallyFactorialDivisors

/--
[weil_iso_cartier_of_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
lemma weil_iso_cartier_of_dedekind
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
-- given
  (hlf : IsLocallyFactorial R) :
-- imply
  Nonempty (CartierDivisorGroup R K ≃* Multiplicative (WeilDivisorGroup R)) :=
-- proof
  ⟨(cartierToWeilMulEquiv K hlf).trans
    (AddEquiv.toMultiplicative (weilDivisorEquiv R)).symm⟩
end LocallyFactorialDivisors
namespace LocallyFactorialDivisors

end LocallyFactorialDivisors

/--
[fractionalIdealToWeil_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma fractionalIdealToWeil_apply_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {I : FractionalIdeal R⁰ K}
  {v : HeightOneSpectrum R} :
-- imply
  (fractionalIdealToWeil K I) v = FractionalIdeal.count K v I := by
-- proof
  apply LocallyFactorialDivisors.fractionalIdealToWeil_apply K I v

/--
[cartierToWeil_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma cartierToWeil_apply_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {u : (FractionalIdeal R⁰ K)ˣ}
  {v : HeightOneSpectrum R} :
-- imply
  (cartierToWeil K u) v = FractionalIdeal.count K v (u : FractionalIdeal R⁰ K) := by
-- proof
  apply LocallyFactorialDivisors.cartierToWeil_apply K u v

/--
[cartierToWeil_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma cartierToWeil_one_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  cartierToWeil K (1 : (FractionalIdeal R⁰ K)ˣ) = 0 := by
-- proof
  apply LocallyFactorialDivisors.cartierToWeil_one K

/--
[cartierToWeil_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma cartierToWeil_mul_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {u₁ u₂ : (FractionalIdeal R⁰ K)ˣ} :
-- imply
  cartierToWeil K (u₁ * u₂) = cartierToWeil K u₁ + cartierToWeil K u₂ := by
-- proof
  apply LocallyFactorialDivisors.cartierToWeil_mul K u₁ u₂

/--
[cartierToWeil_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma cartierToWeil_injective_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  Function.Injective (cartierToWeil (R := R) K) := by
-- proof
  apply LocallyFactorialDivisors.cartierToWeil_injective K

/--
[height_one_coe_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma height_one_coe_ne_zero_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {v : HeightOneSpectrum R} :
-- imply
  (↑v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := by
-- proof
  apply LocallyFactorialDivisors.height_one_coe_ne_zero K v

/--
[weilToCartierIdeal_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma weilToCartierIdeal_ne_zero_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {D : HeightOneSpectrum R →₀ ℤ} :
-- imply
  weilToCartierIdeal K D ≠ 0 := by
-- proof
  apply LocallyFactorialDivisors.weilToCartierIdeal_ne_zero K D

/--
[cartierToWeil_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean)
-/
@[path]
private lemma cartierToWeil_surjective_eq
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  {K : Type*}
  [Field K]
  [Algebra R K]
  [IsFractionRing R K] :
-- imply
  Function.Surjective (cartierToWeil (R := R) K) := by
-- proof
  apply LocallyFactorialDivisors.cartierToWeil_surjective K


-- created on 2026-10-23
