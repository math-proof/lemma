/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part2

@[expose] public section

namespace MetaMathlibExt

/-- Representative map for the counting lemma. -/
def ntRepFun {α : Type*} (r : α → α → Prop) (S : Set α) {m : ℕ}
    (x : Fin m → α) (hxS : ∀ k, x k ∈ S)
    (hcard : ∀ k, 1 < Nat.card ↥(ntCls r (x k))) (k : Fin m) :
    { C : Set α // ∃ x ∈ S, C = ntCls r x ∧ 1 < Nat.card ↥C } :=
  ⟨ntCls r (x k), x k, hxS k, rfl, hcard k⟩

end MetaMathlibExt
