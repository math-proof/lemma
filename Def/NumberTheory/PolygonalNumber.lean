/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PolygonalNumber.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
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

/-- Polygonal-number family: `polygonalNumber s n = (s - 2) * C(n, 2) + n`.

The source's polygonal interpretation assumes `3 ≤ s`; this definition is the
total natural extension to all `s : ℕ`. -/
def polygonalNumber (s n : ℕ) : ℕ := (s - 2) * Nat.choose n 2 + n

end Nat
