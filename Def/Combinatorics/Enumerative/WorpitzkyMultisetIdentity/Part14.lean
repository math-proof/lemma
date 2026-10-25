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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part13


section

namespace MetaMathlibExt

def wmiWordFiberEquiv (m : ℕ) (k : Fin m → ℕ) (p : ℕ) :
    { w : wmiWords m k // wmiDesClass w.1 = p } ≃
      { w : Fin (∑ i, k i) → Fin m //
        (∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i) ∧
        (Finset.univ.filter (fun j : Fin (∑ i, k i) =>
          ∃ h : j.val + 1 < ∑ i, k i,
            w j > w ⟨j.val + 1, h⟩)).card + 1 = p } where
  toFun w := ⟨w.1.1, w.1.2, by simpa [wmiDesClass] using w.2⟩
  invFun w := ⟨⟨w.1, w.2.1⟩, by simpa [wmiDesClass] using w.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
end
