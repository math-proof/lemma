import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.OverpartitionCongruence
open PowerSeries
open scoped PowerSeries.WithPiTopology
open MetaMathlibExt


/--
[overpartition_mul_five_mod_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma overpartition_mul_five_mod_five_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  Int.ModEq 5
    (Nat.card {
    p : Multiset ℕ × Finset ℕ //
    (∀ a ∈ p.1, 0 < a) ∧
    p.1.sum = 5 * n ∧
    ∀ a ∈ p.2, a ∈ p.1
    })
    (((-1 : ℤ) ^ n) * Nat.card {
    x : ℤ × ℤ × ℤ //
    x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = n
    }) := by
-- proof
  apply MetaMathlibExt.overpartition_mul_five_mod_five n hn

/--
[overpartition_card_mul_five_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OverpartitionCongruence.lean)
-/
@[path]
private lemma overpartition_card_mul_five_modEq_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  Int.ModEq 5 (Nat.card (Nat.Overpartition (5 * n)))
    (((-1 : ℤ) ^ n) * Nat.threeSquareRepresentationCount n) := by
-- proof
  apply MetaMathlibExt.overpartition_card_mul_five_modEq n hn


-- created on 2026-10-20
