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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

theorem wmi_card_filter_ofFn {α : Type*} {K : ℕ}
    (f : Fin K → α) (p : α → Prop) [DecidablePred p] :
    ((↑(List.ofFn f) : Multiset α).filter p).card =
      Fintype.card { j : Fin K // p (f j) } := by
  classical
  rw [Fintype.card_subtype]
  induction K with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ]
      change (Multiset.filter p
        (f 0 ::ₘ (↑(List.ofFn fun j : Fin n => f j.succ) : Multiset α))).card = _
      rw [Multiset.filter_cons, Fin.card_filter_univ_succ]
      by_cases h : p (f 0)
      · rw [ite_eq_left h, ite_eq_left h, Multiset.card_add, Multiset.card_singleton,
          ih (fun j => f j.succ)]
        omega
      · rw [ite_eq_right h, ite_eq_right h, zero_add, ih (fun j => f j.succ)]

end MetaMathlibExt
end
