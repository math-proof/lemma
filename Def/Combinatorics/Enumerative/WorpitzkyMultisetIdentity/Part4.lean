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
public import Instance.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

def shiftEquiv {m K x : ℕ} (w : Fin K → Fin m) :
    { e : Fin K → Fin x // IsMono w e } ≃
      { g : Fin K → Fin (x - desPrefix w K) // Monotone g } where
  toFun := fun ⟨e, hmono⟩ => ⟨shiftFwd w e hmono, shiftFwd_mono⟩
  invFun := fun ⟨g, hg⟩ => ⟨shiftBwd w g, shiftBwd_isMono w g hg⟩
  left_inv := fun ⟨e, hmono⟩ =>
    Subtype.ext (shiftFwdBwd w e hmono)
  right_inv := fun ⟨g, hg⟩ =>
    Subtype.ext (shiftBwdFwd w g hg)

/-- Multiset of a tuple, via `List.ofFn`. -/
def monoToSym {α : Type*} [LinearOrder α] {K : ℕ}
    (f : Fin K → α) : Sym α K :=
  ⟨↑(List.ofFn f), by rw [Multiset.coe_card, List.length_ofFn]⟩

end MetaMathlibExt
end
