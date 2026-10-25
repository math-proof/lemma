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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part5


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
