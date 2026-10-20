/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Minpoly/IntegrallyClosed.lean -/

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed

/-!
# Integrality over an integrally closed domain via minimal polynomials

For an integrally closed domain `R` with fraction field `K` and a field extension `L`
of `K`, an element of `L` algebraic over `K` is integral over `R` if and only if its
`K`-minimal polynomial lifts to `R`, equivalently every coefficient lies in the range
of `algebraMap R K`.
-/

variable {R K L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

namespace minpoly

/-- An element of `L` algebraic over `K` is integral over `R` iff its `K`-minimal
polynomial lifts to `R`. -/
theorem isIntegral_iff_mem_lifts {x : L} (hx : IsAlgebraic K x) :
    IsIntegral R x ↔ minpoly K x ∈ Polynomial.lifts (algebraMap R K) := by
  constructor
  · intro h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K h]
    exact Polynomial.mem_lifts _ |>.mpr ⟨_, rfl⟩
  · intro h
    obtain ⟨q, hq, -, hqmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic h (minpoly.monic hx.isIntegral)
    refine ⟨q, hqmonic, ?_⟩
    have hroot : Polynomial.aeval x (minpoly K x) = 0 := minpoly.aeval K x
    rw [← hq] at hroot
    rwa [Polynomial.aeval_map_algebraMap] at hroot

/-- An element of `L` algebraic over `K` is integral over `R` iff every coefficient
of its `K`-minimal polynomial lies in the range of `algebraMap R K`. -/
theorem isIntegral_iff_coeff_mem_range {x : L} (hx : IsAlgebraic K x) :
    IsIntegral R x ↔ ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K) := by
  rw [isIntegral_iff_mem_lifts hx, Polynomial.lifts_iff_coeff_lifts]

end minpoly
