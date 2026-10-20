import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.PrimitiveDivisor
open scoped BigOperators
open LucasSequence


/--
[IsPrimitiveDivisor.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_pos_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  0 < n := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.pos h

/--
[IsPrimitiveDivisor.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_prime_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  p.Prime := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.prime h

/--
[IsPrimitiveDivisor.dvd_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_dvd_term_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  (p : ℤ) ∣ u n := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.dvd_term h

/--
[IsPrimitiveDivisor.not_dvd_badPart](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_not_dvd_badPart_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.not_dvd_badPart h

/--
[IsPrimitiveDivisor.not_dvd_discriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_not_dvd_discriminant_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p) :
-- imply
  ¬(p : ℤ) ∣ discriminant := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.not_dvd_discriminant h

/--
[IsPrimitiveDivisor.not_dvd_prior](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_not_dvd_prior_eq
  {u : ℕ → ℤ}
  {discriminant : ℤ}
  {n p k : ℕ}
-- given
  (h : IsPrimitiveDivisor u discriminant n p)
  (hk : k ∈ Finset.Ico 1 n) :
-- imply
  ¬(p : ℤ) ∣ u k := by
-- proof
  apply LucasSequence.IsPrimitiveDivisor.not_dvd_prior h hk


-- created on 2026-10-20
