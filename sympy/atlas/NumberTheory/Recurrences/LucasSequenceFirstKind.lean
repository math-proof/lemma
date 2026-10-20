/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/LucasSequenceFirstKind.lean -/

import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

/-!
# Lucas sequence of the first kind

Source-faithful recurrence predicate for the Lucas sequence of the first
kind with integer parameters.

Provenance:
- stable record: `jis_grounded_7e37bcd48e7477bda602ca6e`
- frozen source: `https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`
- file SHA-256: `eb765815f14b18e047ccd51b0ed4ec17305d9410f60516b290425a6cd7a49d05`
- exact UTF-8 bytes 3175-3840, lines 114-122
- span SHA-256: `dce48c9908ba3e56bb82b2792cbb734d489dc1558763f1c1284855dc2de7ea4f`

The source fixes integers `P Q` and imposes `u 0 = 0`, `u 1 = 1`, and
`u (n + 2) = P * u (n + 1) - Q * u n` for every `n`. It discusses Binet
formulas separately, so this predicate records the recurrence directly.
-/

/--
`IsLucasSequenceFirstKind P Q u` holds exactly when `u` satisfies the
Lucas sequence of the first kind recurrence with parameters `P Q`:
`u 0 = 0`, `u 1 = 1`, and `u (n + 2) = P * u (n + 1) - Q * u n` for all `n`.

Provenance: stable record `jis_grounded_7e37bcd48e7477bda602ca6e`,
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`,
lines 114-122.
-/
def IsLucasSequenceFirstKind (P Q : ℤ) (u : ℕ → ℤ) : Prop :=
  u 0 = 0 ∧ u 1 = 1 ∧ ∀ n : ℕ, u (n + 2) = P * u (n + 1) - Q * u n

/-- First clause of the defining recurrence: the value at `0`. -/
theorem IsLucasSequenceFirstKind.initialZero {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) : u 0 = 0 :=
  h.1

/-- Second clause of the defining recurrence: the value at `1`. -/
theorem IsLucasSequenceFirstKind.initialOne {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) : u 1 = 1 :=
  h.2.1

/-- Third clause of the defining recurrence: the two-step relation. -/
theorem IsLucasSequenceFirstKind.recurrenceStep {P Q : ℤ} {u : ℕ → ℤ}
    (h : IsLucasSequenceFirstKind P Q u) (n : ℕ) :
    u (n + 2) = P * u (n + 1) - Q * u n :=
  h.2.2 n

end MetaMathlibExt
