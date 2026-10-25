/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaSequence.lean -/

import Mathlib.Data.Nat.Basic
/-!
# Narayana's cows sequence

Formalizes the Narayana sequence from the Journal of Integer Sequences.
- Concept: `jis_sem_cf6cb7757b3800269bff893c` ("narayana sequence").
- Source statement: `jis_e95687510f34475587245fbb`.
- Source: `jis_source_f83f1af8a3d625820c162c43`
  (`https://cs.uwaterloo.ca/journals/JIS/VOL23/Das/bravo17.tex`).
-/


namespace MetaMathlibExt

/-- Narayana's cows sequence `(N_n)_{n ≥ 0}`: `N_0 = 0`, `N_1 = N_2 = 1`, and
`N_n = N_{n-1} + N_{n-3}` for `n ≥ 3`.

Concept `jis_sem_cf6cb7757b3800269bff893c`; source statement
`jis_e95687510f34475587245fbb` in source `jis_source_f83f1af8a3d625820c162c43`. -/
def narayanaCowsSequence : Nat → Nat
  | Nat.zero => Nat.zero
  | Nat.succ Nat.zero => Nat.succ Nat.zero
  | Nat.succ (Nat.succ Nat.zero) => Nat.succ Nat.zero
  | Nat.succ (Nat.succ (Nat.succ n)) =>
    narayanaCowsSequence (Nat.succ (Nat.succ n)) + narayanaCowsSequence n

end MetaMathlibExt
