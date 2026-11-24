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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

/-- Sorted enumeration is monotone. -/
theorem symToMono_mono {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : Monotone (symToMono S) := by
  have hsort : (S.val.sort (· ≤ ·)).Pairwise (· ≤ ·) :=
    Multiset.pairwise_sort _ _
  have hmono : Monotone (S.val.sort (· ≤ ·)).get :=
    hsort.sortedLE.monotone_get
  intro a b hab
  have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.mp hab
  have hcast : Fin.cast (symSortLength S).symm a ≤
      Fin.cast (symSortLength S).symm b := by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_cast]
    exact hab'
  exact hmono hcast

/-- Sorting a sorted tuple is identity. -/
theorem sort_ofFn_eq {α : Type*} [LinearOrder α] {K : ℕ}
    (f : Fin K → α) (hf : Monotone f) :
    ((↑(List.ofFn f) : Multiset α).sort (· ≤ ·)) = List.ofFn f := by
  rw [Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hf.sortedLE_ofFn.pairwise

theorem wmi_monoToSym_symToMono {α : Type*} [LinearOrder α] {K : ℕ}
    (S : Sym α K) : monoToSym (symToMono S) = S := by
  apply Sym.ext
  change (↑(List.ofFn (symToMono S)) : Multiset α) = S.val
  have hlist : List.ofFn (symToMono S) = S.val.sort (· ≤ ·) := by
    change List.ofFn (fun j => (S.val.sort (· ≤ ·)).get
      (Fin.cast (symSortLength S).symm j)) = S.val.sort (· ≤ ·)
    simpa only [List.ofFn_get] using
      (List.ofFn_congr (symSortLength S) (S.val.sort (· ≤ ·)).get).symm
  rw [hlist, Multiset.sort_eq]

theorem wmi_monoToSym_injective {α : Type*} [LinearOrder α] {K : ℕ} :
    Function.Injective
      (fun f : { f : Fin K → α // Monotone f } => monoToSym f.1) := by
  intro f g hfg
  apply Subtype.ext
  apply List.ofFn_injective
  have hvals : (monoToSym f.1).val = (monoToSym g.1).val :=
    congrArg (fun S : Sym α K => S.val) hfg
  change (↑(List.ofFn (f : Fin K → α)) : Multiset α) =
    ↑(List.ofFn (g : Fin K → α)) at hvals
  have hsorted := congrArg (fun s : Multiset α => s.sort (· ≤ ·)) hvals
  rw [sort_ofFn_eq (f := (f : Fin K → α)) f.2,
    sort_ofFn_eq (f := (g : Fin K → α)) g.2] at hsorted
  exact hsorted

end MetaMathlibExt
end
