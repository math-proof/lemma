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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

theorem wmi_content_iff_filter {m K x : ℕ} (k : Fin m → ℕ)
    (f : Fin K → (Fin x ×ₗ Fin m)) :
    (∀ i, Fintype.card { j : Fin K // (ofLex (f j)).2 = i } = k i) ↔
      ∀ i, ((monoToSym f).val.filter
        (fun q => (ofLex q).2 = i)).card = k i := by
  constructor
  · intro h i
    change ((↑(List.ofFn f) : Multiset (Fin x ×ₗ Fin m)).filter
      (fun q => (ofLex q).2 = i)).card = k i
    exact (wmi_card_filter_ofFn f (fun q => (ofLex q).2 = i)).trans (h i)
  · intro h i
    rw [← wmi_card_filter_ofFn f (fun q => (ofLex q).2 = i)]
    exact h i

end MetaMathlibExt
end
