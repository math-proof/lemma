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
public import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part3

@[expose] public section

namespace MetaMathlibExt

/-- Forward map on image subtypes. -/
def ntImgFwd {α β : Type*} (f : β → α) (s : Set β) (a : ↥s) : ↥(f '' s) :=
  ⟨f a.1, a.1, a.2, rfl⟩

end MetaMathlibExt
