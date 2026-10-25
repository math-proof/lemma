import Mathlib
import sympy.Basic
import Def.NumberTheory.PrimeCounting.ResidueClass
open Nat


namespace Nat

/--
[primeCountingMod_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean)
-/
@[path]
lemma primeCountingMod_one
  {X a : ℕ} :
-- imply
  primeCountingMod X 1 a = Nat.primeCounting X := by
-- proof
  unfold primeCountingMod
  have hfilter : (X.primesLE.filter fun p => p ≡ a [MOD 1]) = X.primesLE := by
    apply Finset.filter_true_of_mem
    intro p _
    simp [Nat.ModEq, Nat.mod_one]
  rw [hfilter, Nat.primesLE_card_eq_primeCounting]

end Nat

namespace Nat

/--
[primeCountingMod_eq_card_filter_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ResidueClass.lean)
-/
@[path]
lemma primeCountingMod_eq_card_filter_range
  {n q a : ℕ} :
-- imply
  primeCountingMod n q a
    = ((Finset.range (n + 1)).filter
    fun p => Nat.Prime p ∧ Nat.ModEq q p a).card := by
-- proof
  unfold Nat.primeCountingMod
  rw [Nat.primesLE_eq_filter_range, Finset.filter_filter]

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
