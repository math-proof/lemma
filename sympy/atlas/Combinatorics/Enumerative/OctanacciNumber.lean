/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/OctanacciNumber.lean -/

import Mathlib.Data.Nat.Basic

/-!
# Octanacci numbers

The order-eight all-ones Fibonacci sequence appears in Emanuele Munarini,
*Shifting Property for Riordan, Sheffer and Connection Constants Matrices*,
and Tian-Xiao He, *Impulse Response Sequences and Construction of Number
Sequence Identities*.
-/

namespace MetaMathlibExt

/-- A sliding window `(f n, ..., f (n+7))` for the octanacci sequence. -/
def octanacciWindow : Nat → Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
  | 0 => (1, 1, 2, 4, 8, 16, 32, 64)
  | n + 1 =>
    match octanacciWindow n with
    | (a, b, c, d, e, f, g, h) =>
      (b, c, d, e, f, g, h, a + b + c + d + e + f + g + h)

/-- The octanacci sequence `1, 1, 2, 4, 8, 16, 32, 64, 128, 255, ...`,
whose generating function is `1 / (1 - t - ... - t^8)`.

Stable source identifiers: concept `jis_sem_89f2f2ec1c72d6db5f92b1d0`;
statements `jis_cb7e03aa435f1bbd253660ca` and
`jis_f311834ff91269ae7cf94a4b`.
-/
def octanacciNumber (n : Nat) : Nat :=
  (octanacciWindow n).1

end MetaMathlibExt
