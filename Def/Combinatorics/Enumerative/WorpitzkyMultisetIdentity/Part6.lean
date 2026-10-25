/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part5


section

namespace MetaMathlibExt

/-- Monotone tuples are the sorted enumerations of multisets. -/
def wmiMonoEquivSym {α : Type*} [LinearOrder α] {K : ℕ} :
    { f : Fin K → α // Monotone f } ≃ Sym α K where
  toFun f := monoToSym f
  invFun S := ⟨symToMono S, symToMono_mono S⟩
  left_inv f := by
    apply wmi_monoToSym_injective
    exact wmi_monoToSym_symToMono (monoToSym (f : Fin K → α))
  right_inv := wmi_monoToSym_symToMono

end MetaMathlibExt
end
