module
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Fintype.Fin
public import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
