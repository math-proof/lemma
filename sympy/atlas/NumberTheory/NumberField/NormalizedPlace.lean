/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/NormalizedPlace.lean -/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import sympy.atlas.Analysis.AbsoluteValue.Rpow
/-!
# Degree-normalized places of a number field

For a number field `K` of degree `d = [K : ℚ]`, this file provides the
degree-normalized finite and infinite absolute values used in height theory.
At a finite place the exponent is `1 / d`, because Mathlib's raw finite absolute value already
incorporates the local degree through the ideal norm. At an infinite place the exponent is
`mult v / d`, where `mult v` is one at a real place and two at a complex place.

The product formula for these normalized values is a separate result and is not asserted here.

## References

* [T. Hilgart and V. Ziegler, *On a conjecture of Levesque and
  Waldschmidt*](https://arxiv.org/abs/2306.11331v1)
* [S. Akhtari, J. D. Vaaler, and M. Widmer, *Small integral generators of totally complex number
  fields*](https://arxiv.org/abs/2307.11849v6)
-/

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The degree-normalized absolute value at a finite place.

Mathlib's raw finite absolute value already contains the local-degree factor, so the remaining
normalization exponent is `1 / [K : ℚ]`. -/
noncomputable def FinitePlace.normalizedAbsoluteValue (v : FinitePlace K) :
    AbsoluteValue K ℝ := by
  refine v.val.rpow (1 / (Module.finrank ℚ K : ℝ)) ?_ ?_
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    positivity
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    rw [div_le_one hfinrank]
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)

/-- Evaluation of the degree-normalized absolute value at a finite place. -/
@[simp]
theorem FinitePlace.normalizedAbsoluteValue_apply (v : FinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [FinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, FinitePlace.coe_apply]

/-- The degree-normalized finite-place value expressed through Mathlib's canonical `adicAbv`. -/
theorem FinitePlace.normalizedAbsoluteValue_apply_eq_adicAbv (v : FinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x =
      (HeightOneSpectrum.adicAbv K v.maximalIdeal x) ^
        (1 / (Module.finrank ℚ K : ℝ)) := by
  rw [FinitePlace.normalizedAbsoluteValue_apply,
    ← FinitePlace.norm_embedding v.maximalIdeal x, FinitePlace.norm_embedding_eq]

/-- The degree-normalized absolute value at an infinite place. -/
noncomputable def InfinitePlace.normalizedAbsoluteValue (v : InfinitePlace K) :
    AbsoluteValue K ℝ := by
  refine v.val.rpow ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) ?_ ?_
  · have hmult : 0 < (v.mult : ℝ) := by
      exact_mod_cast InfinitePlace.mult_pos (w := v)
    have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    positivity
  · have hfinrank : 0 < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
    rw [div_le_one hfinrank]
    exact_mod_cast calc
      v.mult ≤ ∑ w : InfinitePlace K, w.mult :=
        Finset.single_le_sum (fun w _ => Nat.zero_le w.mult) (Finset.mem_univ v)
      _ = Module.finrank ℚ K := InfinitePlace.sum_mult_eq

/-- Evaluation of the degree-normalized absolute value at an infinite place. -/
@[simp]
theorem InfinitePlace.normalizedAbsoluteValue_apply (v : InfinitePlace K) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ ((v.mult : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  rw [InfinitePlace.normalizedAbsoluteValue, AbsoluteValue.rpow_apply, InfinitePlace.coe_apply]

/-- At a real place, the degree-normalization exponent is `1 / [K : ℚ]`. -/
theorem InfinitePlace.normalizedAbsoluteValue_apply_of_isReal (v : InfinitePlace K)
    (hv : v.IsReal) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  simp [hv.mult_eq_one]

/-- At a complex place, the degree-normalization exponent is `2 / [K : ℚ]`. -/
theorem InfinitePlace.normalizedAbsoluteValue_apply_of_isComplex (v : InfinitePlace K)
    (hv : v.IsComplex) (x : K) :
    v.normalizedAbsoluteValue x = v x ^ (2 / (Module.finrank ℚ K : ℝ)) := by
  simp [hv.mult_eq_two]

end NumberField
