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
public import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

def wmiPackSym {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    wmiPairSymData m (∑ i, k i) x k :=
  ⟨⟨wmiPack k S, wmiPack_card k S⟩, fun i => by
    change ((wmiPack k S).filter (fun q => (ofLex q).2 = i)).card = k i
    rw [wmiPack_filter, Multiset.card_map, (S i).2]⟩

def wmiUnpack {m x : ℕ} (k : Fin m → ℕ)
    (M : wmiPairSymData m (∑ i, k i) x k) :
    ∀ i, Sym (Fin x) (k i) :=
  fun i =>
    ⟨M.1.val.filter (fun q => (ofLex q).2 = i) |>.map
        (fun q => (ofLex q).1),
      by rw [Multiset.card_map, M.2 i]⟩

end MetaMathlibExt
end
