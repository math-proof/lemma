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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part10


section

namespace MetaMathlibExt

theorem wmiPack_card {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) :
    (wmiPack k S).card = ∑ i, k i := by
  unfold wmiPack
  rw [Multiset.card_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Multiset.card_map, (S i).2]

theorem wmi_filter_finset_sum {ι α : Type*} (p : α → Prop)
    [DecidablePred p] (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s, f i).filter p = ∑ i ∈ s, (f i).filter p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.sum_insert ha]

theorem wmiPack_filter {m x : ℕ} (k : Fin m → ℕ)
    (S : ∀ i, Sym (Fin x) (k i)) (i : Fin m) :
    (wmiPack k S).filter (fun q => (ofLex q).2 = i) =
      (S i).val.map (fun v => toLex (v, i)) := by
  classical
  unfold wmiPack
  rw [wmi_filter_finset_sum]
  simp only [Multiset.filter_map]
  rw [Finset.sum_eq_single i]
  · congr 1
    apply Multiset.filter_eq_self.mpr
    intro a _
    rfl
  · intro b _ hbi
    simp [hbi]
  · simp

end MetaMathlibExt
end
