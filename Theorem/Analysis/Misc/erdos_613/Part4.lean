import Mathlib
import Def.Analysis.Misc.erdos_613.Part6
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

/-- Partition of the red neighbors of {name}`apex` into the two blocks. -/
lemma redBlocks_partition_card (color : Sym2 V → Fin 2) :
  (redBlock1 color).card + (redBlock2 color).card = (redNeighbors color).card := by
  classical
  -- Standard `filter` + `filter (¬p)` partition identity.
  simpa [redBlock1, redBlock2] using
    (Finset.card_filter_add_card_filter_not
      (s := redNeighbors color) (p := fun v => inBlock1 v))

/-- **Pigeonhole step.** If there is no blue `K_{1,5}`, then
one of the two blocks receives at least six red edges from {name}`apex`. -/
lemma exists_block_receives_at_least_6_red
    (color : Sym2 V → Fin 2)
    (hNoBlueStar : ¬ hasMonoStar G color 0 5) :
    (redBlock1 color).card ≥ 6 ∨ (redBlock2 color).card ≥ 6 := by
  classical
  -- Total red edges from `apex` is at least 11 (done earlier).
  have h11 : 11 ≤ (redNeighbors color).card :=
    red_from_apex_at_least_11 color hNoBlueStar
  -- Split red neighbors across the two blocks.
  have hsum := redBlocks_partition_card color
  -- If both blocks had ≤ 5, then the total would be ≤ 10 — contradiction.
  by_contra h
  push_neg at h   -- h : (redBlock1 color).card ≤ 5 ∧ (redBlock2 color).card ≤ 5
  have hle10 : (redNeighbors color).card ≤ 10 := by
    have : (redBlock1 color).card + (redBlock2 color).card ≤ 5 + 5 := by
      grind
    simpa [hsum] using this
  exact (Nat.not_succ_le_self 10) (le_trans h11 hle10)

end PikhurkoN5
