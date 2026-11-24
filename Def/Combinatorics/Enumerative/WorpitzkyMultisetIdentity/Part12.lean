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
public import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

def wmiTuplePairSymEquiv (m x : ℕ) (k : Fin m → ℕ) :
    (∀ i, Sym (Fin x) (k i)) ≃
      wmiPairSymData m (∑ i, k i) x k where
  toFun := wmiPackSym k
  invFun := wmiUnpack k
  left_inv := wmiUnpack_pack k
  right_inv := wmiPack_unpack k

def wmiTupleWordEquiv (m x : ℕ) (k : Fin m → ℕ) :
    (∀ i, Sym (Fin x) (k i)) ≃
      wmiWordData m (∑ i, k i) x k :=
  (wmiTuplePairSymEquiv m x k).trans
    ((wmiPairSymEquiv m (∑ i, k i) x k).symm.trans
      (wmiWordPairEquiv m (∑ i, k i) x k).symm)

end MetaMathlibExt
end
