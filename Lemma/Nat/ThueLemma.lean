import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ThueLemma
open MetaMathlibExt


/--
[thue_lemma_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThueLemma.lean)
-/
@[path]
private lemma thue_lemma_general_eq
  {a n : ℤ}
-- given
  (hn : 1 < n)
  (hcop : Int.gcd a n = 1) :
-- imply
  ∃ x y : ℤ,
    (0 : ℤ) < |x| ∧ (|x| : ℝ) < Real.sqrt (n : ℝ) ∧
    (0 : ℤ) < |y| ∧ (|y| : ℝ) < Real.sqrt (n : ℝ) ∧ x ≡ a * y [ZMOD n] := by
-- proof
  apply MetaMathlibExt.thue_lemma_general a n hn hcop

/--
[thue_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ThueLemma.lean)
-/
@[path]
private lemma thue_lemma_eq
  {a n : ℤ}
-- given
  (ha : 1 < a)
  (hn : 1 < n)
  (hcop : Int.gcd a n = 1) :
-- imply
  ∃ x y : ℤ,
    (0 : ℤ) < |x| ∧ (|x| : ℝ) < Real.sqrt (n : ℝ) ∧
    (0 : ℤ) < |y| ∧ (|y| : ℝ) < Real.sqrt (n : ℝ) ∧ x ≡ a * y [ZMOD n] := by
-- proof
  apply MetaMathlibExt.thue_lemma a n ha hn hcop


-- created on 2026-10-20
