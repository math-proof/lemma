/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theorem.Combinatorics.BellWeakExcedance.Part10


section

namespace MetaMathlibExt

noncomputable def bwe_validPermEquivFinpartition (n : ℕ) :
    { σ : Equiv.Perm (Fin n) //
      ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } ≃
      Finpartition (Finset.univ : Finset (Fin n)) where
  toFun σ := toPart n σ
  invFun P := ⟨ofPartPerm P, ofPartPerm_valid P⟩
  left_inv σ := by
    apply Subtype.ext
    exact bwe_ofPartPerm_toPart σ.property
  right_inv P := toPart_ofPartPerm P

end MetaMathlibExt
end
