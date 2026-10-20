import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NormalNumberSequence
open MetaMathlibExt


/--
[normalSeq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
private lemma normalSeq_one_eq
  {a1 a2 : ℤ} :
-- imply
  normalSeq a1 a2 1 = 1 := by
-- proof
  apply MetaMathlibExt.normalSeq_one a1 a2

/--
[normalSeq_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
private lemma normalSeq_two_eq
  {a1 a2 : ℤ} :
-- imply
  normalSeq a1 a2 2 = a1 := by
-- proof
  apply MetaMathlibExt.normalSeq_two a1 a2

/--
[normalSeq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
private lemma normalSeq_recurrence_eq
  {a1 a2 : ℤ}
  {n : ℕ} :
-- imply
  normalSeq a1 a2 (n + 2) =
    a1 * normalSeq a1 a2 (n + 1) + a2 * normalSeq a1 a2 n := by
-- proof
  apply MetaMathlibExt.normalSeq_recurrence a1 a2 n

/--
[normalSeqFib_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
private lemma normalSeqFib_add_eq
  {a : ℤ}
  {m n : ℕ} :
-- imply
  normalSeqFib a (m + n + 1) =
    normalSeqFib a (m + 1) * normalSeqFib a (n + 1) +
    normalSeqFib a m * normalSeqFib a n := by
-- proof
  apply MetaMathlibExt.normalSeqFib_add a m n

/--
[normalSeq_odd_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NormalNumberSequence.lean)
-/
@[path]
private lemma normalSeq_odd_identity_eq
  {a : ℤ}
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  normalSeqFib a (2 * n - 1) =
    (normalSeqFib a n) ^ 2 + (normalSeqFib a (n - 1)) ^ 2 := by
-- proof
  apply MetaMathlibExt.normalSeq_odd_identity a n hn


-- created on 2026-10-20
