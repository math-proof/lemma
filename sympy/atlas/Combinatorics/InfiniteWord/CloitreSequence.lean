/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/CloitreSequence.lean -/

import Mathlib.Order.Monotone.Basic

/-!
# Cloitre's self-describing sequence

Concept definitions for Cloitre's self-describing sequence (OEIS A157196):
run-sum divided by 2 recovers the sequence, constructed as the limit of
`A_{k+1} = A_k A_k^r` with `A_0 = [1, 1]`.
-/

namespace MetaMathlibExt

/-- First-letter complement at run-letter level over flat `1`/`2` lists.

Sends `[2, ..]` to `[1, 1, ..]` and `[1, 1, ..]` to `[2, ..]`; the remaining
branch is unreachable on the approximants below (every `A_k` starts with
`1, 1`, and every approximant tail used here starts with `1, 1` or `2`).
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreComplementFirst : List ℕ → List ℕ
  | [] => []
  | 2 :: xs => 1 :: 1 :: xs
  | 1 :: 1 :: xs => 2 :: xs
  | x :: xs => x :: xs

/-- Mirror image with first-letter complementation: `A^r`.

Reverses `A` and flips its first run-letter (`[1, 1] ↔ [2]`). For example
`[1, 1, 2]^r = [1, 1, 1, 1]` and `[1, 1, 2, 1, 1, 1, 1]^r = [2, 1, 1, 2, 1, 1]`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreMirror (A : List ℕ) : List ℕ :=
  cloitreComplementFirst A.reverse

/-- Paperfolding approximants: `A_0 = [1, 1]`, `A_{k+1} = A_k ++ (A_k)^r`.

Unrolls as `A_0 = [1, 1]`, `A_1 = [1, 1, 2]`,
`A_2 = [1, 1, 2, 1, 1, 1, 1]`,
`A_3 = [1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1]`, continuing `2, 2, …`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreApprox : ℕ → List ℕ
  | 0 => [1, 1]
  | k + 1 => cloitreApprox k ++ cloitreMirror (cloitreApprox k)

/-- Limit sequence read off the approximants.

Each approximant extends the previous one and `|A_{n+2}| > n`, so position
`n` is stable from stage `n + 2` onward; out-of-range lookup defaults to `0`.
Beginning: `1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, …`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreSequence (n : ℕ) : ℕ :=
  (cloitreApprox (n + 2)).getD n 0

/-- Maximal-run boundary for a sequence `s`: `b 0 = 0`, `b` strictly
monotone (so the blocks `[b n, b (n+1))` exhaust `ℕ`), constant on each
block, with adjacent blocks taking distinct values.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def IsRunBoundary (s : ℕ → ℕ) (b : ℕ → ℕ) : Prop :=
  b 0 = 0 ∧
    StrictMono b ∧
    (∀ n i j, b n ≤ i → i < b (n + 1) → b n ≤ j → j < b (n + 1) → s i = s j) ∧
    (∀ n i j, b n ≤ i → i < b (n + 1) →
      b (n + 1) ≤ j → j < b (n + 2) → s i ≠ s j)

/-- Finite sum of `s` over the `n`th run `[b n, b (n+1))`.
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def cloitreRunSum (s : ℕ → ℕ) (b : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((List.range (b (n + 1) - b n)).map (fun i => s (b n + i))).sum

/-- Self-description: run-sums are twice the original sequence.

There is a run boundary `b` with `2 * s n =` run-sum over block `n` for every
`n`, avoiding truncated `Nat` division (e.g. run-sums
`2, 2, 4, 2, 2, 2, 2, 4, …` halve to `1, 1, 2, 1, 1, 1, 1, 2, …`).
Source `jis_38a9669323eb3fad1c972241`, `jis_dec34d24d6807862a9e836cc`. -/
def IsCloitreSelfDescribing (s : ℕ → ℕ) : Prop :=
  ∃ b, IsRunBoundary s b ∧ ∀ n, 2 * s n = cloitreRunSum s b n

end MetaMathlibExt
