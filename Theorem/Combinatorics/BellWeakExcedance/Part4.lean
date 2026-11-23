/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Combinatorics.Enumerative.Bell
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Def.Combinatorics.BellWeakExcedance.Part4

@[expose] public section

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
