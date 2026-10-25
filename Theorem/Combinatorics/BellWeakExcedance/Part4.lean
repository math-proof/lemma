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
import Def.Combinatorics.BellWeakExcedance.Part4


section

namespace MetaMathlibExt

theorem mem_toPart_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {a b : Fin n} :
    b ∈ (toPart n σ).part a ↔ root n σ a = root n σ b := by
  unfold toPart
  classical
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

theorem root_eq_self_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} {i : Fin n} :
    root n σ i = i ↔ i ∈ wexSet n σ := by
  constructor
  · intro h
    rw [← h]
    exact root_mem n σ i
  · intro h
    exact root_eq_self n σ i h

end MetaMathlibExt
end
