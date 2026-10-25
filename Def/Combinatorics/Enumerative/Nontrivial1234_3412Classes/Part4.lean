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
import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part3


namespace MetaMathlibExt

/-- Forward map on image subtypes. -/
def ntImgFwd {α β : Type*} (f : β → α) (s : Set β) (a : ↥s) : ↥(f '' s) :=
  ⟨f a.1, a.1, a.2, rfl⟩

end MetaMathlibExt
