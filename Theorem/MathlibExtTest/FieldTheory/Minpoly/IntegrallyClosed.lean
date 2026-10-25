/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Minpoly/IntegrallyClosed.lean -/


import Lemma.Rat.Minpoly.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-!
# Tests for integrality via minimal polynomials over integrally closed domains
-/


/-- Forward direction of the lifts characterization. -/
example {x : L} (hx : IsAlgebraic K x) (h : IsIntegral R x) :
    minpoly K x ∈ Polynomial.lifts (algebraMap R K) :=
  (minpoly.isIntegral_iff_mem_lifts hx).mp h

/-- Backward direction of the lifts characterization. -/
example {x : L} (hx : IsAlgebraic K x)
    (h : minpoly K x ∈ Polynomial.lifts (algebraMap R K)) : IsIntegral R x :=
  (minpoly.isIntegral_iff_mem_lifts hx).mpr h

/-- Forward direction of the coefficient-range characterization. -/
example {x : L} (hx : IsAlgebraic K x) (h : IsIntegral R x) (n : ℕ) :
    (minpoly K x).coeff n ∈ Set.range (algebraMap R K) :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mp h n

/-- Backward direction of the coefficient-range characterization. -/
example {x : L} (hx : IsAlgebraic K x)
    (h : ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K)) :
    IsIntegral R x :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mpr h

/-- An integer-cast rational is integral, so its rational minimal polynomial lifts. -/
example (n : ℤ) (hx : IsAlgebraic ℚ ((n : ℤ) : ℚ)) :
    minpoly ℚ ((n : ℤ) : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) :=
  (minpoly.isIntegral_iff_mem_lifts hx).mp (isIntegral_intCast n)

/-- Every coefficient of the minimal polynomial of an integer-cast rational lies in
the range of the integer map. -/
example (n : ℤ) (hx : IsAlgebraic ℚ ((n : ℤ) : ℚ)) (m : ℕ) :
    (minpoly ℚ ((n : ℤ) : ℚ)).coeff m ∈ Set.range (algebraMap ℤ ℚ) :=
  (minpoly.isIntegral_iff_coeff_mem_range hx).mp (isIntegral_intCast n) m

