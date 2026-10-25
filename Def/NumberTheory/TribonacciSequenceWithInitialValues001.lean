/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TribonacciSequenceWithInitialValues001.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Tribonacci sequence with initial values 0, 0, 1

This module records the JIS concept `jis_sem_1b39589c4b5afc1c43ad6e8e`.
-/


namespace MetaMathlibExt

/-- The Tribonacci sequence `0, 0, 1, 1, 2, 4, …` (OEIS A000073).

Source: Jiaqiang Pan, *Multiple Binomial Transforms and Families of Integer Sequences*,
Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Pan/pan8.tex>.

JIS source statements: `jis_16c3a95646fb4f21e9695b73`,
`jis_6d169983fc890fcb1432ab1e`, and `jis_91386fd90045523def73af3f`.
-/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n

end MetaMathlibExt
