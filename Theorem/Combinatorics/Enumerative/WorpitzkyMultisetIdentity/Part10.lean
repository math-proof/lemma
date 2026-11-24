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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
