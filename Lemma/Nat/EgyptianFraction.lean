import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EgyptianFraction
open scoped BigOperators
open EgyptianFraction
open IsNondecreasingEgyptian
open IsStrictEgyptian
open IsNondecreasingUnderapproximation
open IsStrictUnderapproximation


/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma denominator_ge_two_eq
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i := by
-- proof
  apply EgyptianFraction.IsNondecreasingEgyptian.denominator_ge_two h i

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma monotone_eq
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  Monotone a := by
-- proof
  apply EgyptianFraction.IsNondecreasingEgyptian.monotone h

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictEgyptian_denominator_ge_two_eq
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i := by
-- proof
  apply EgyptianFraction.IsStrictEgyptian.denominator_ge_two h i

/--
[strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma strictMono_eq
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  StrictMono a := by
-- proof
  apply EgyptianFraction.IsStrictEgyptian.strictMono h

/--
[toIsNondecreasingEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma toIsNondecreasingEgyptian_eq
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  IsNondecreasingEgyptian a := by
-- proof
  apply EgyptianFraction.IsStrictEgyptian.toIsNondecreasingEgyptian h

/--
[nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma nonempty_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < n := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.nonempty h

/--
[target_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma target_pos_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < target := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.target_pos h

/--
[isNondecreasingEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma isNondecreasingEgyptian_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  IsNondecreasingEgyptian a := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.isNondecreasingEgyptian h

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsNondecreasingUnderapproximation_denominator_ge_two_eq
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.denominator_ge_two h i

/--
[monotone](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsNondecreasingUnderapproximation_monotone_eq
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  Monotone a := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.monotone h

/--
[sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma sum_lt_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  ∑ i, ((a i : ℝ)⁻¹) < target := by
-- proof
  apply EgyptianFraction.IsNondecreasingUnderapproximation.sum_lt h

/--
[nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictUnderapproximation_nonempty_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < n := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.nonempty h

/--
[target_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictUnderapproximation_target_pos_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  0 < target := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.target_pos h

/--
[isStrictEgyptian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma isStrictEgyptian_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictUnderapproximation target a) :
-- imply
  IsStrictEgyptian a := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.isStrictEgyptian h

/--
[denominator_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictUnderapproximation_denominator_ge_two_eq
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsNondecreasingEgyptian a) :
-- imply
  2 ≤ a i := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.denominator_ge_two h i

/--
[strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictUnderapproximation_strictMono_eq
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictEgyptian a) :
-- imply
  StrictMono a := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.strictMono h

/--
[sum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma EgyptianFraction_IsStrictUnderapproximation_sum_lt_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsNondecreasingUnderapproximation target a) :
-- imply
  ∑ i, ((a i : ℝ)⁻¹) < target := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.sum_lt h

/--
[toIsNondecreasingUnderapproximation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean)
-/
@[path]
private lemma toIsNondecreasingUnderapproximation_eq
  {n : ℕ}
  {target : ℝ}
  {a : Fin n → ℕ}
-- given
  (h : IsStrictUnderapproximation target a) :
-- imply
  IsNondecreasingUnderapproximation target a := by
-- proof
  apply EgyptianFraction.IsStrictUnderapproximation.toIsNondecreasingUnderapproximation h


-- created on 2026-10-20
