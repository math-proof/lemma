/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean -/

import Mathlib.Data.Nat.Basic

namespace MetaMathlibExt

/-- Josephus survivor function `J_k` (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clauses `domain`, `meaning`): the one-based
position of the sole survivor when every `k`th person is eliminated from a
circle of `n` people. Defined by structural recursion on the population: the
value at `0` is `0` purely as the recursion anchor (public theorems retain the
source domain `2 ≤ k` and `1 ≤ n`); successors use the one-based Euler
recurrence. -/
def josephus (k : Nat) : Nat → Nat
  | 0 => 0
  | (n + 1) => ((josephus k n + k - 1) % (n + 1)) + 1

/-- Base case `J_k(1) = 1` (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `base`). The hypothesis `_hk` records the
source domain `k ≥ 2` and is unused by the proof. -/
theorem josephus_one (k : Nat) (_hk : 2 ≤ k) : josephus k 1 = 1 := by
  simp only [josephus]
  omega

/-- One-based Euler recurrence (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `euler_recurrence`): for `n ≥ 1`,
`J_k(n+1) = ((J_k(n) + k - 1) mod (n+1)) + 1`. The hypotheses `_hk` and `_hn`
record the source domain `k ≥ 2`, `n ≥ 1` and are unused by the proof. -/
theorem josephus_succ (k n : Nat) (_hk : 2 ≤ k) (_hn : 1 ≤ n) :
    josephus k (n + 1) = ((josephus k n + k - 1) % (n + 1)) + 1 := by
  simp only [josephus]

/-- Range `J_k(n) ∈ [[1, n]]` (concept `jis_sem_e1c9a353312d2a1564410d6e`;
source statements `jis_1986849a138b5f4709dd284a`, `jis_2b78f59babf40128fececb65`,
`jis_597f2ddde7f055cc80cc8489`, `jis_cddd7a6b10023809e13a6c78`,
`jis_fe4f24c64ecfdad23577e877`; clause `range`): for every `n ≥ 1`,
`1 ≤ J_k(n)` and `J_k(n) ≤ n`. The hypothesis `_hk` records the source domain
`k ≥ 2` and is unused by the proof. -/
theorem josephus_range (k n : Nat) (_hk : 2 ≤ k) (hn : 1 ≤ n) :
    1 ≤ josephus k n ∧ josephus k n ≤ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : josephus k (m + 1) = ((josephus k m + k - 1) % (m + 1)) + 1 := by
    simp only [josephus]
  rw [h]
  constructor
  · omega
  · have hpos : 0 < m + 1 := by omega
    have hmod : (josephus k m + k - 1) % (m + 1) < m + 1 :=
      Nat.mod_lt _ hpos
    omega

end MetaMathlibExt
