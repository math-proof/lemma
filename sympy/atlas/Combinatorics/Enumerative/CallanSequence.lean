/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CallanSequence.lean -/

import Mathlib.Data.Finset.Empty

namespace MetaMathlibExt

/-- Unbarred `Callan sequence` of size `k × n` (concept
`jis_term_ce5e63b2f9fff90839347b2c`, statement `jis_9bd5ee64b3776e07257d0f5f`,
source `jis_source_076226dadb590961d2a14ace`, lines 159-190).

The blue base set `{1, …, k} ∪ {*}` is represented as `Option (Fin k)` with
`none` the distinguished blue star, and likewise the red base set is
`Option (Fin n)` with `none` the red star. The `m + 1` ordered Callan pairs
are indexed by `Fin (m + 1)`, with `Fin.last m` indexing the extra pair
`(B⋆, R⋆)` that contains both stars. Each colour's blocks are nonempty and
every base-set element belongs to exactly one block. -/
structure CallanSequence (k n : ℕ) where
  /-- Number of ordinary Callan pairs. -/
  m : ℕ
  /-- Pair-count bound from the source definition. -/
  m_le_n : m ≤ n
  /-- Blue blocks indexed by `Fin (m + 1)`. -/
  blue : Fin (m + 1) → Finset (Option (Fin k))
  /-- Red blocks indexed by `Fin (m + 1)`. -/
  red : Fin (m + 1) → Finset (Option (Fin n))
  /-- Every blue block is nonempty. -/
  blue_nonempty : ∀ i, (blue i).Nonempty
  /-- Every red block is nonempty. -/
  red_nonempty : ∀ i, (red i).Nonempty
  /-- The blue blocks partition the blue base set. -/
  blue_covers : ∀ x, ∃! i, x ∈ blue i
  /-- The red blocks partition the red base set. -/
  red_covers : ∀ x, ∃! i, x ∈ red i
  /-- The blue star lies in the extra blue block. -/
  blue_mem_star : (none : Option (Fin k)) ∈ blue (Fin.last m)
  /-- The red star lies in the extra red block. -/
  red_mem_star : (none : Option (Fin n)) ∈ red (Fin.last m)

end MetaMathlibExt
