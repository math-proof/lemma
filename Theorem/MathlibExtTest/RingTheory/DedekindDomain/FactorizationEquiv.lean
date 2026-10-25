/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/FactorizationEquiv.lean -/


import Def.RingTheory.DedekindDomain.FactorizationEquiv.Part4
import Lemma.Int.DedekindDomain.FactorizationEquiv
open scoped nonZeroDivisors

open IsDedekindDomain FractionalIdeal

/-!
# Tests for the prime-exponent equivalence of fractional ideals

Examples exercising `FractionalIdeal.factorizationMulEquiv`: identity,
single-prime basis and reconstruction, and multiplication/addition of valuations.
-/


namespace MathlibExtTest.RingTheory.DedekindDomain.FactorizationEquiv

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable (K)

/-- Identity: the unit ideal has vanishing prime exponents. -/
example : Multiplicative.toAdd (factorizationMulEquiv K (1 : (FractionalIdeal R⁰ K)ˣ)) = 0 :=
  unitsToFinsupp_one K

/-- Identity: the equivalence sends `1` to `1`. -/
example : factorizationMulEquiv K (1 : (FractionalIdeal R⁰ K)ˣ) = 1 :=
  map_one (factorizationMulEquiv K)

/-- Identity round trip on units. -/
example (u : (FractionalIdeal R⁰ K)ˣ) :
    (factorizationMulEquiv K).symm (factorizationMulEquiv K u) = u :=
  (factorizationMulEquiv K).left_inv u

/-- Single-prime basis: a prime ideal maps to the corresponding basis function. -/
example (w : HeightOneSpectrum R) :
    Multiplicative.toAdd
        (factorizationMulEquiv K
          (Units.mk0 _ (coeIdeal_ne_zero.mpr w.ne_bot))) =
      Finsupp.single w 1 :=
  factorizationMulEquiv_prime_self K w

/-- Single-prime basis evaluates to `1` on the diagonal. -/
example (w : HeightOneSpectrum R) :
    Multiplicative.toAdd
        (factorizationMulEquiv K
          (Units.mk0 _ (coeIdeal_ne_zero.mpr w.ne_bot))) w = 1 := by
  rw [factorizationMulEquiv_prime_self K w, Finsupp.single_eq_same]

/-- Single-prime reconstruction: decoding `n` at `w` recovers the prime power. -/
example (w : HeightOneSpectrum R) (n : ℤ) :
    (↑((factorizationMulEquiv K).symm (Multiplicative.ofAdd (Finsupp.single w n))) :
      FractionalIdeal R⁰ K) = (w.asIdeal : FractionalIdeal R⁰ K) ^ n :=
  symm_single_zpow K w n

/-- Single-prime round trip: encoding then decoding recovers the exponent. -/
example (w : HeightOneSpectrum R) (n : ℤ) :
    FractionalIdeal.count K w
      ((factorizationMulEquiv K).symm (Multiplicative.ofAdd (Finsupp.single w n))) = n := by
  rw [symm_single_zpow, FractionalIdeal.count_zpow_self]

/-- The equivalence preserves multiplication. -/
example (u v : (FractionalIdeal R⁰ K)ˣ) :
    factorizationMulEquiv K (u * v) =
      factorizationMulEquiv K u * factorizationMulEquiv K v :=
  (factorizationMulEquiv K).map_mul u v

/-- Valuations add under multiplication, seen through the equivalence. -/
example (u v : (FractionalIdeal R⁰ K)ˣ) (w : HeightOneSpectrum R) :
    Multiplicative.toAdd (factorizationMulEquiv K (u * v)) w =
      Multiplicative.toAdd (factorizationMulEquiv K u) w +
        Multiplicative.toAdd (factorizationMulEquiv K v) w := by
  rw [map_mul, toAdd_mul, Finsupp.add_apply]

/-- Exponents add under multiplication, as finitely supported functions. -/
example (u v : (FractionalIdeal R⁰ K)ˣ) :
    unitsToFinsupp K (u * v) = unitsToFinsupp K u + unitsToFinsupp K v :=
  unitsToFinsupp_mul K u v

end MathlibExtTest.RingTheory.DedekindDomain.FactorizationEquiv
