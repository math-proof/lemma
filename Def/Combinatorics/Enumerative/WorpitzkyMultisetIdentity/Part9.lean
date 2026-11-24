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
public import Abbrev.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
