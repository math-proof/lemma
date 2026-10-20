import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimitiveDivisor
open IntegerSequence


/--
[IsPrimitiveDivisor.one_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_one_le_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  1 ≤ m := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.one_le h

/--
[IsPrimitiveDivisor.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_two_le_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  2 ≤ u := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.two_le h

/--
[IsPrimitiveDivisor.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_dvd_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u) :
-- imply
  (u : ℤ) ∣ a m := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.dvd h

/--
[IsPrimitiveDivisor.not_dvd_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_not_dvd_of_lt_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
  {s : ℕ}
-- given
  (h : IsPrimitiveDivisor a m u)
  (hs : 1 ≤ s)
  (hsm : s < m) :
-- imply
  ¬ (u : ℤ) ∣ a s := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.not_dvd_of_lt h hs hsm

/--
[IsPrimitivePrimeDivisor.prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_prime_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  Nat.Prime u := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.prime h

/--
[IsPrimitivePrimeDivisor.toIsPrimitiveDivisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_toIsPrimitiveDivisor_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  IsPrimitiveDivisor a m u := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.toIsPrimitiveDivisor h

/--
[IsPrimitivePrimeDivisor.one_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_one_le_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  1 ≤ m := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.one_le h

/--
[IsPrimitivePrimeDivisor.two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_two_le_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  2 ≤ u := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.two_le h

/--
[IsPrimitivePrimeDivisor.dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_dvd_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u) :
-- imply
  (u : ℤ) ∣ a m := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.dvd h

/--
[IsPrimitivePrimeDivisor.not_dvd_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_not_dvd_of_lt_eq
  {a : ℕ → ℤ}
  {m u : ℕ}
  {s : ℕ}
-- given
  (h : IsPrimitivePrimeDivisor a m u)
  (hs : 1 ≤ s)
  (hsm : s < m) :
-- imply
  ¬ (u : ℤ) ∣ a s := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.not_dvd_of_lt h hs hsm

/--
[isPrimitivePrimeDivisor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma isPrimitivePrimeDivisor_iff_eq
  {a : ℕ → ℤ}
  {m u : ℕ} :
-- imply
  IsPrimitivePrimeDivisor a m u ↔
      Nat.Prime u ∧ 1 ≤ m ∧ 2 ≤ u ∧ (u : ℤ) ∣ a m ∧
        ∀ s : ℕ, 1 ≤ s → s < m → ¬ (u : ℤ) ∣ a s := by
-- proof
  apply IntegerSequence.isPrimitivePrimeDivisor_iff

/--
[IsPrimitiveDivisor.le_of_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_le_of_dvd_eq
  {a : ℕ → ℤ}
  {m u n : ℕ}
-- given
  (hm : IsPrimitiveDivisor a m u)
  (hn : 1 ≤ n)
  (hdvd : (u : ℤ) ∣ a n) :
-- imply
  m ≤ n := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.le_of_dvd hm hn hdvd

/--
[IsPrimitiveDivisor.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitiveDivisor_unique_eq
  {a : ℕ → ℤ}
  {m n u : ℕ}
-- given
  (hm : IsPrimitiveDivisor a m u)
  (hn : IsPrimitiveDivisor a n u) :
-- imply
  m = n := by
-- proof
  apply IntegerSequence.IsPrimitiveDivisor.unique hm hn

/--
[IsPrimitivePrimeDivisor.unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimitiveDivisor.lean)
-/
@[path]
private lemma IsPrimitivePrimeDivisor_unique_eq
  {a : ℕ → ℤ}
  {m n u : ℕ}
-- given
  (hm : IsPrimitivePrimeDivisor a m u)
  (hn : IsPrimitivePrimeDivisor a n u) :
-- imply
  m = n := by
-- proof
  apply IntegerSequence.IsPrimitivePrimeDivisor.unique hm hn


-- created on 2026-10-20
