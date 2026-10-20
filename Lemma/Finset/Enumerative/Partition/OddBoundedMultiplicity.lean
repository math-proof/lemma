import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.OddBoundedMultiplicity
open MetaMathlibExt


/--
[card_odd_countRestricted_four_eq_card_mod_four_pair_excluding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/OddBoundedMultiplicity.lean)
-/
@[path]
private lemma card_odd_countRestricted_four_eq_card_mod_four_pair_excluding_eq
  {n : ℕ} :
-- imply
  (Nat.Partition.odds n ∩ Nat.Partition.countRestricted n 4).card =
    (Finset.univ.filter fun p : Nat.Partition n ↦
    (∀ i ∈ p.parts, i % 4 = 1 ∨ i % 4 = 3) ∧
    ∀ j ∈ Finset.range (n + 1),
    ¬ (4 * j + 1 ∈ p.parts ∧ 4 * j + 3 ∈ p.parts)).card := by
-- proof
  apply MetaMathlibExt.card_odd_countRestricted_four_eq_card_mod_four_pair_excluding n


-- created on 2026-10-20
