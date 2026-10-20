import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.IntegerComplexity
open Expr
open IntegerComplexity


/--
[eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma eval_one_eq
  :
-- imply
  (one : Expr).eval = 1 := by
-- proof
  apply IntegerComplexity.Expr.eval_one

/--
[count_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma count_one_eq
  :
-- imply
  (one : Expr).count = 1 := by
-- proof
  apply IntegerComplexity.Expr.count_one

/--
[eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma eval_add_eq
  {a b : Expr} :
-- imply
  (add a b).eval = a.eval + b.eval := by
-- proof
  apply IntegerComplexity.Expr.eval_add a b

/--
[eval_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma eval_mul_eq
  {a b : Expr} :
-- imply
  (mul a b).eval = a.eval * b.eval := by
-- proof
  apply IntegerComplexity.Expr.eval_mul a b

/--
[count_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma count_add_eq
  {a b : Expr} :
-- imply
  (add a b).count = a.count + b.count := by
-- proof
  apply IntegerComplexity.Expr.count_add a b

/--
[count_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma count_mul_eq
  {a b : Expr} :
-- imply
  (mul a b).count = a.count + b.count := by
-- proof
  apply IntegerComplexity.Expr.count_mul a b

/--
[count_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma count_pos_eq
  {e : Expr} :
-- imply
  0 < e.count := by
-- proof
  apply IntegerComplexity.Expr.count_pos e

/--
[eval_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma eval_pos_eq
  {e : Expr} :
-- imply
  0 < e.eval := by
-- proof
  apply IntegerComplexity.Expr.eval_pos e

/--
[exists_expr_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma exists_expr_of_pos_eq
  {n : ℕ}
-- given
  (h : 0 < n) :
-- imply
  ∃ e : Expr, e.eval = n := by
-- proof
  apply IntegerComplexity.exists_expr_of_pos h

/--
[exists_expr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma exists_expr_eq
  {n : ℕ+} :
-- imply
  ∃ e : Expr, e.eval = n.val := by
-- proof
  apply IntegerComplexity.exists_expr n

/--
[Pred_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma Pred_nonempty_eq
  {n : ℕ+} :
-- imply
  ∃ c, Pred n c := by
-- proof
  apply IntegerComplexity.Pred_nonempty n

/--
[complexity_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_spec_eq
  {n : ℕ+} :
-- imply
  Pred n (complexity n) := by
-- proof
  apply IntegerComplexity.complexity_spec n

/--
[complexity_min_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_min_le_eq
  {n : ℕ+}
  {m : ℕ}
-- given
  (hm : Pred n m) :
-- imply
  complexity n ≤ m := by
-- proof
  apply IntegerComplexity.complexity_min_le n hm

/--
[exists_optimal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma exists_optimal_eq
  {n : ℕ+} :
-- imply
  ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = complexity n := by
-- proof
  apply IntegerComplexity.exists_optimal n

/--
[complexity_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_le_eq
  {n : ℕ+}
  {e : Expr}
-- given
  (he : e.eval = (n : ℕ)) :
-- imply
  complexity n ≤ e.count := by
-- proof
  apply IntegerComplexity.complexity_le he

/--
[complexity_le_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_le_count_eq
  {n : ℕ+}
  {e : Expr}
-- given
  (he : e.eval = (n : ℕ)) :
-- imply
  complexity n ≤ e.count := by
-- proof
  apply IntegerComplexity.complexity_le_count n e he

/--
[one_le_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma one_le_complexity_eq
  {n : ℕ+} :
-- imply
  1 ≤ complexity n := by
-- proof
  apply IntegerComplexity.one_le_complexity n

/--
[complexity_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_one_eq
  :
-- imply
  complexity (1 : ℕ+) = 1 := by
-- proof
  apply IntegerComplexity.complexity_one

/--
[complexity_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_add_le_eq
  {a b : ℕ+} :
-- imply
  complexity (a + b) ≤ complexity a + complexity b := by
-- proof
  apply IntegerComplexity.complexity_add_le a b

/--
[complexity_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
private lemma complexity_mul_le_eq
  {a b : ℕ+} :
-- imply
  complexity (a * b) ≤ complexity a + complexity b := by
-- proof
  apply IntegerComplexity.complexity_mul_le a b


-- created on 2026-10-20
