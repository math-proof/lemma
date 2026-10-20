import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.RogersRamanujan
open scoped PowerSeries.WithPiTopology
open MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted


/--
[rogers_ramanujan_difference_two_vs_one_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RogersRamanujan.lean)
-/
@[path]
private lemma rogers_ramanujan_difference_two_vs_one_four_eq
  {n : ℕ} :
-- imply
  (Finset.univ.filter (fun p : Nat.Partition n =>
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b)).card =
    (Finset.univ.filter (fun p : Nat.Partition n =>
    ∀ m ∈ p.parts, m % 5 = 1 ∨ m % 5 = 4)).card := by
-- proof
  apply MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted.rogers_ramanujan_difference_two_vs_one_four n


-- created on 2026-10-20
