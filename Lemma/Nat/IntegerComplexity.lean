import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.IntegerComplexity.Part3
open Expr
open IntegerComplexity


namespace IntegerComplexity.Expr

/--
[complexity_spec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_spec
  {n : ℕ+} :
-- imply
  Pred n (complexity n) := by
-- proof
  classical
  exact Nat.find_spec (Pred_nonempty n)

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[complexity_min_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_min_le
  {n : ℕ+}
  {m : ℕ}
-- given
  (hm : Pred n m) :
-- imply
  complexity n ≤ m := by
-- proof
  classical
  exact Nat.find_min' (Pred_nonempty n) hm

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[exists_optimal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma exists_optimal
  {n : ℕ+} :
-- imply
  ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = complexity n :=
-- proof
  complexity_spec n

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[complexity_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_le
  {n : ℕ+}
  {e : Expr}
-- given
  (he : e.eval = (n : ℕ)) :
-- imply
  complexity n ≤ e.count :=
-- proof
  complexity_min_le n ⟨e, he, rfl⟩

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[complexity_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_one
  :
-- imply
  complexity (1 : ℕ+) = 1 := by
-- proof
  apply Nat.le_antisymm
  · exact complexity_min_le _ ⟨.one, rfl, rfl⟩
  · obtain ⟨e, _, hcount⟩ := exists_optimal (1 : ℕ+)
    have hpos := e.count_pos
    omega

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[complexity_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_add_le
  {a b : ℕ+} :
-- imply
  complexity (a + b) ≤ complexity a + complexity b := by
-- proof
  obtain ⟨ea, hea, hca⟩ := exists_optimal a
  obtain ⟨eb, heb, hcb⟩ := exists_optimal b
  have h : (Expr.add ea eb).eval = ((a + b : ℕ+) : ℕ) := by simp [hea, heb, PNat.add_coe]
  have hle := complexity_le h
  simp only [count_add, hca, hcb, ge_iff_le] at hle ⊢
  exact hle

end IntegerComplexity.Expr

namespace IntegerComplexity.Expr

/--
[complexity_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_mul_le
  {a b : ℕ+} :
-- imply
  complexity (a * b) ≤ complexity a + complexity b := by
-- proof
  obtain ⟨ea, hea, hca⟩ := exists_optimal a
  obtain ⟨eb, heb, hcb⟩ := exists_optimal b
  have h : (Expr.mul ea eb).eval = ((a * b : ℕ+) : ℕ) := by simp [hea, heb, PNat.mul_coe]
  have hle := complexity_le h
  simp only [count_mul, hca, hcb, ge_iff_le] at hle ⊢
  exact hle

end IntegerComplexity.Expr

/--
[count_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma count_pos
  {e : Expr} :
-- imply
  0 < e.count := by
-- proof
  induction e with
  | one => simp [count]
  | add a b iha ihb => simp only [count]; exact Nat.add_pos_left iha _
  | mul a b iha ihb => simp only [count]; exact Nat.add_pos_left iha _


namespace IntegerComplexity.Expr

/--
[eval_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma eval_pos
  {e : Expr} :
-- imply
  0 < e.eval := by
-- proof
  induction e with
  | one => simp [eval]
  | add a b iha ihb => simp only [eval]; exact Nat.add_pos_left iha _
  | mul a b iha ihb => simp only [eval]; exact Nat.mul_pos iha ihb
open Expr

end IntegerComplexity.Expr

namespace IntegerComplexity

/--
[complexity_le_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma complexity_le_count
  {n : ℕ+}
  {e : Expr}
-- given
  (he : e.eval = (n : ℕ)) :
-- imply
  complexity n ≤ e.count :=
-- proof
  complexity_le he

end IntegerComplexity

namespace IntegerComplexity

/--
[one_le_complexity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean)
-/
@[path]
lemma one_le_complexity
  {n : ℕ+} :
-- imply
  1 ≤ complexity n := by
-- proof
  obtain ⟨e, _, hcount⟩ := exists_optimal n
  have hpos := e.count_pos
  omega

end IntegerComplexity

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


-- created on 2026-10-20
-- updated on 2026-10-26
