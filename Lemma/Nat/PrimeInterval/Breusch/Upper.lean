import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch.Upper
open Nat Finset
open MathlibExt.NumberTheory.BreuschWanted.Internal


/--
[G9_zero9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9_zero9_eq
  :
-- imply
  ∀ j < 9, G9 j = 0 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9_zero9

/--
[G9_at9](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9_at9_eq
  :
-- imply
  G9 9 = 1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9_at9

/--
[G9_small_le1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9_small_le1_eq
  :
-- imply
  ∀ j < 10, G9 j ≤ 1 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9_small_le1

/--
[G9r_le3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9r_le3_eq
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  G9r x ≤ 3 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9r_le3 x hx

/--
[G9r_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9r_vanish_eq
  {x : ℝ}
-- given
  (hx0 : 0 ≤ x)
  (hx : x < 1 / ((10 * Q9 : ℕ) : ℝ)) :
-- imply
  G9r x = 0 := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9r_vanish x hx0 hx

/--
[G9r_level1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9r_level1_eq
  {x : ℝ}
-- given
  (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x)
  (h : 1 ≤ G9r x) :
-- imply
  (279 : ℝ) / 18900 ≤ x := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9r_level1 x hx h

/--
[G9r_level2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9r_level2_eq
  {x : ℝ}
-- given
  (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x)
  (h : 2 ≤ G9r x) :
-- imply
  (657 : ℝ) / 18900 ≤ x := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9r_level2 x hx h

/--
[G9r_level3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma G9r_level3_eq
  {x : ℝ}
-- given
  (hx : 1 / ((9 * Q9 : ℕ) : ℝ) ≤ x)
  (h : 3 ≤ G9r x) :
-- imply
  (963 : ℝ) / 18900 ≤ x := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.G9r_level3 x hx h

/--
[logF9_upper](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Upper.lean)
-/
@[path]
private lemma logF9_upper_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hA : ∀ p : ℕ, p.Prime → 1890 * n < p → p ≤ 2100 * n → False) :
-- imply
  logF9 n ≤ (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * n * Real.log 3.4
    + Real.sqrt (2100 * n) * Real.log (2100 * n) := by
-- proof
  apply MathlibExt.NumberTheory.BreuschWanted.Internal.logF9_upper n hn hA


-- created on 2026-10-20
