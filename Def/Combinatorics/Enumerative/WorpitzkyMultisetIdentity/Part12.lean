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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part11


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
