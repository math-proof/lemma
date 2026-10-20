import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.ResidueClass
open Nat


/--
[primeCountingMod_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean)
-/
@[path]
private lemma primeCountingMod_one_eq
  {X a : ℕ} :
-- imply
  primeCountingMod X 1 a = Nat.primeCounting X := by
-- proof
  apply Nat.primeCountingMod_one X a

/--
[primeCountingMod_eq_card_filter_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean)
-/
@[path]
private lemma primeCountingMod_eq_card_filter_range_eq
  {n q a : ℕ} :
-- imply
  primeCountingMod n q a
      = ((Finset.range (n + 1)).filter
        fun p => Nat.Prime p ∧ Nat.ModEq q p a).card := by
-- proof
  apply Nat.primeCountingMod_eq_card_filter_range n q a


-- created on 2026-10-20
