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
import Abbrev.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part3


section

namespace MetaMathlibExt

def wmiPairMonoSymEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiPairMonoData m K x k ≃ wmiPairSymData m K x k :=
  Equiv.subtypeEquiv
    (wmiMonoEquivSym (α := Fin x ×ₗ Fin m) (K := K)) fun f => by
      change (∀ i, Fintype.card { j : Fin K // (ofLex (f.1 j)).2 = i } = k i) ↔
        ∀ i, ((monoToSym f.1).val.filter
          (fun q => (ofLex q).2 = i)).card = k i
      exact wmi_content_iff_filter k f.1

def wmiPairSymEquiv (m K x : ℕ) (k : Fin m → ℕ) :
    wmiPairData m K x k ≃ wmiPairSymData m K x k :=
  (wmiPairDataNestEquiv m K x k).trans (wmiPairMonoSymEquiv m K x k)

end MetaMathlibExt
end
