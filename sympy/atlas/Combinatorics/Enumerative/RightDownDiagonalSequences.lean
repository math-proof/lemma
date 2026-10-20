/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RightDownDiagonalSequences.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Right-down diagonal sequences

This file formalizes the recurrence in László Németh and László Szalay,
*Sequences Involving Square Zig-Zag Shapes*, Journal of Integer Sequences 24
(2021), Article 21.5.2.
-/

open scoped BigOperators

namespace MetaMathlibExt

/-- The coefficient `(-1)^i * choose (k+1-i) (i+1)` in the right-down
diagonal recurrence. -/
def rightDownDiagonalCoefficient (k i : ℕ) : ℤ :=
  (-1) ^ i * Nat.choose (k + 1 - i) (i + 1)

/-- A family of right-down diagonal sequences of order `k`.

The family index has type `Fin (k+2)`, exactly representing source indices
`0, ..., k+1`. Stable source identifiers: concept
`jis_sem_81073f165e7dac1ef20a1a7a`, statement
`jis_0034612dbd4f4faf5fca455c`.
-/
def IsRightDownDiagonalFamily (k : ℕ) (A : Fin (k + 2) → ℕ → ℤ) : Prop :=
  1 ≤ k ∧ ∀ j n, k / 2 + 1 ≤ n →
    A j n = ∑ i ∈ Finset.range (k / 2 + 1),
      rightDownDiagonalCoefficient k i * A j (n - 1 - i)

end MetaMathlibExt
