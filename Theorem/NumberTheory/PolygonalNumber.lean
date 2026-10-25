/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Def.NumberTheory.PolygonalNumber
/-!
# Polygonal numbers

This file formalizes the polygonal-number family from Zhi-Wei Sun's
"On universal sums of polygonal numbers" (Sci. China Math. 58 (2015), 1367--1396).

The source defines, for `m = 3, 4, ...` and `n = 0, 1, 2, ...`,
`p_m(n) = (m - 2) * C(n, 2) + n`.

The source's geometric polygonal interpretation assumes `3 ≤ s`.
The Lean definition below is the total natural-number extension of that
binomial formula to all `s : ℕ`, using `Nat.choose` so no unintended
truncated-subtraction semantics enter the definition itself.
-/


namespace Nat

/-- Total-extension initial value at `0`; the source claims this only for `3 ≤ s`. -/
@[simp] theorem polygonalNumber_zero (s : ℕ) : polygonalNumber s 0 = 0 := by
  have h : Nat.choose 0 2 = 0 := by decide
  simp [polygonalNumber, h]

/-- Total-extension initial value at `1`; the source claims this only for `3 ≤ s`. -/
@[simp] theorem polygonalNumber_one (s : ℕ) : polygonalNumber s 1 = 1 := by
  have h : Nat.choose 1 2 = 0 := by decide
  simp only [polygonalNumber, h]
  simp

end Nat
