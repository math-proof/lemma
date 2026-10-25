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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part7


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
