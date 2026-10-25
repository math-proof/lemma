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
import Instance.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part2


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
