import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.HonsbergerFibonacciP
open MetaMathlibExt


/--
[fibonacciP_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma fibonacciP_zero_eq
  {p : ℕ} :
-- imply
  fibonacciP p 0 = 0 := by
-- proof
  apply MetaMathlibExt.fibonacciP_zero p

/--
[fibonacciP_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma fibonacciP_eq_one_eq
  {p r : ℕ}
-- given
  (hr : 1 ≤ r)
  (hrp : r ≤ p) :
-- imply
  fibonacciP p r = 1 := by
-- proof
  apply MetaMathlibExt.fibonacciP_eq_one p r hr hrp

/--
[fibonacciP_rec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma fibonacciP_rec_eq
  {p r : ℕ}
-- given
  (hpr : p < r) :
-- imply
  fibonacciP p r = fibonacciP p (r - 1) + fibonacciP p (r - p - 1) := by
-- proof
  apply MetaMathlibExt.fibonacciP_rec p r hpr

/--
[fibonacciP_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma fibonacciP_one_eq
  {n : ℕ} :
-- imply
  fibonacciP 1 n = Nat.fib n := by
-- proof
  apply MetaMathlibExt.fibonacciP_one n

/--
[honsberger_fibonacciP](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HonsbergerFibonacciP.lean)
-/
@[path]
private lemma honsberger_fibonacciP_eq
  {p m n : ℕ}
-- given
  (hp : 0 < p)
  (hm_pos : 0 < m)
  (hn_pos : 0 < n)
  (hm : p ≤ m + 1)
  (hn : p ≤ n + 2) :
-- imply
  fibonacciP p 0 = 0 →
    (∀ r, 1 ≤ r → r ≤ p → fibonacciP p r = 1) →
    (∀ r, p < r →
    fibonacciP p r =
    fibonacciP p (r - 1) + fibonacciP p (r - p - 1)) →
    fibonacciP p (m + 1) * fibonacciP p (n + 2) +
    ∑ j ∈ Finset.range p,
    fibonacciP p (m + 1 - (j + 1)) *
    fibonacciP p (n + (j + 1) + 1 - p) =
    fibonacciP p (m + n + 2) := by
-- proof
  apply MetaMathlibExt.honsberger_fibonacciP p m n hp hm_pos hn_pos hm hn


-- created on 2026-10-20
