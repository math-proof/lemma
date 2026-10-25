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
import Theorem.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part10


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
