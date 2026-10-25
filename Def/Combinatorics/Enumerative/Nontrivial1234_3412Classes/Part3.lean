/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part2


namespace MetaMathlibExt

/-- Representative map for the counting lemma. -/
def ntRepFun {α : Type*} (r : α → α → Prop) (S : Set α) {m : ℕ}
    (x : Fin m → α) (hxS : ∀ k, x k ∈ S)
    (hcard : ∀ k, 1 < Nat.card ↥(ntCls r (x k))) (k : Fin m) :
    { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨ntCls r (x k), x k, hxS k, rfl, hcard k⟩

end MetaMathlibExt
