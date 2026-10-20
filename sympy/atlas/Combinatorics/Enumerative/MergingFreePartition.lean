/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MergingFreePartition.lean -/

import Mathlib.Data.Finset.Basic

namespace MetaMathlibExt

/-- Merging-free partition over `Fin n` in slash-ordered block representation.

Concept `jis_sem_b7c50ba5c98632f7e1692f88`, source `jis_source_6a539d4a69c1cba832a9f1a4`,
statement `jis_a73f3b4e90f7919cc07e8594`: every block is nonempty, blocks are
pairwise disjoint and cover all of `Fin n`; block minima are strictly increasing
in list order; for every adjacent pair, the maximum of the earlier block exceeds
the minimum of the later block. -/
def IsMergingFreePartition (n : ℕ) (P : List (Finset (Fin n))) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
    P.Pairwise (fun B C => B ∩ C = ∅) ∧
    (∀ x, ∃ B ∈ P, x ∈ B) ∧
    P.Pairwise (fun B C =>
      ∃ mB ∈ B, ∃ mC ∈ C,
        (∀ b ∈ B, mB ≤ b) ∧ (∀ c ∈ C, mC ≤ c) ∧ mB < mC) ∧
    P.IsChain (fun B C =>
      ∃ mC ∈ C, ∃ mB ∈ B,
        (∀ c ∈ C, mC ≤ c) ∧ (∀ b ∈ B, b ≤ mB) ∧ mC < mB)

end MetaMathlibExt
