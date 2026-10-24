/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SulankeNumber.lean -/

import Mathlib.Tactic

namespace MetaMathlibExt

/-!
# Sulanke number arrays

This module formalizes the recursive arrays in JIS statement
`jis_a908be719d10c77849cc63c2`, Pita,
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Pita/pita5.tex>, lines 1000–1051,
SHA-256 `2c3262137bb1ab4f5170f7cd1e9f38693d8ffa606fe189765b7f3ee0444ef7ed`.
Concept `jis_term_faad96daf465b7809dfe63ad`, semantic concept
`jis_sem_3fe7bd1b4773dd5d0cab4515`.
-/

/-- Sulanke `B` array from the JIS clause: `B 0 = (1, 0, ...)`,
`B (k+1)` is built from `B k` by eliminating the intermediate `A` row,
so `B (k+1) 0 = B k 0` and
`B (k+1) (i+1) = (B k (i+1) + 2 * B k i) + (B k i + 2 * B k (i - 1))`
with the value below zero read as `0`. -/
def sulankeB : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => sulankeB k 0
  | k + 1, n + 1 =>
    (sulankeB k (n + 1) + 2 * sulankeB k n) +
      (sulankeB k n + 2 * match n with | 0 => (0 : ℕ) | m + 1 => sulankeB k m)

/-- Sulanke `A` array from the JIS clause: `A 0 = 0` and
`A (k+1) i = B k i + 2 * B k (i - 1)` with the value below zero
read as `0`. -/
def sulankeA : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, 0 => sulankeB k 0
  | k + 1, n + 1 => sulankeB k (n + 1) + 2 * sulankeB k n
end MetaMathlibExt
