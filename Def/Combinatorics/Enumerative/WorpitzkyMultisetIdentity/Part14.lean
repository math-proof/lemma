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
public import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
