import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Padics.HilbertSymbol.Real
open realHilbertSymbol


/--
[eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma eq_one_iff_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ↔
    ∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 := by
-- proof
  apply realHilbertSymbol.eq_one_iff

/--
[eq_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma eq_neg_one_iff_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔
    ¬∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 := by
-- proof
  apply realHilbertSymbol.eq_neg_one_iff

/--
[eq_neg_one_iff_both_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma eq_neg_one_iff_both_neg_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
-- proof
  apply realHilbertSymbol.eq_neg_one_iff_both_neg

/--
[eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma eq_one_or_neg_one_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b = 1 ∨ realHilbertSymbol a b = -1 := by
-- proof
  apply realHilbertSymbol.eq_one_or_neg_one a b

/--
[sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma sq_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ^ 2 = 1 := by
-- proof
  apply realHilbertSymbol.sq a b

/--
[ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol/Real.lean)
-/
@[path]
private lemma ne_zero_eq
  {a b : ℝˣ} :
-- imply
  realHilbertSymbol a b ≠ 0 := by
-- proof
  apply realHilbertSymbol.ne_zero a b


-- created on 2026-10-20
