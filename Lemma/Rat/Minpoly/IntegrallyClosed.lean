import Mathlib
import Initialize.Tactic.Attr.Basic


namespace minpoly

/--
[isIntegral_iff_mem_lifts](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Minpoly/IntegrallyClosed.lean)
-/
@[path]
lemma isIntegral_iff_mem_lifts
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  {x : L}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  IsIntegral R x ↔ minpoly K x ∈ Polynomial.lifts (algebraMap R K) := by
-- proof
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

end minpoly

namespace minpoly

/--
[isIntegral_iff_coeff_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Minpoly/IntegrallyClosed.lean)
-/
@[path]
lemma isIntegral_iff_coeff_mem_range
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  {x : L}
-- given
  (hx : IsAlgebraic K x) :
-- imply
  IsIntegral R x ↔ ∀ n, (minpoly K x).coeff n ∈ Set.range (algebraMap R K) := by
-- proof
  rw [isIntegral_iff_mem_lifts hx, Polynomial.lifts_iff_coeff_lifts]

end minpoly


-- created on 2026-10-20
-- updated on 2026-10-26
