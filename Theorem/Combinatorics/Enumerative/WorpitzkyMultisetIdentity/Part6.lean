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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part6


section

namespace MetaMathlibExt

theorem wmi_desPrefix_eq_sum_range {m K : ℕ} (w : Fin K → Fin m)
    (n : ℕ) :
    desPrefix w n = ∑ j ∈ Finset.range n, desInd w j := by
  induction n with
  | zero => simp [desPrefix_zero]
  | succ n ih => simp [desPrefix_succ, Finset.sum_range_succ, ih]

theorem wmi_desPrefix_eq_card {m K : ℕ} (w : Fin K → Fin m) :
    desPrefix w K =
      (Finset.univ.filter (fun j : Fin K =>
        ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card := by
  rw [wmi_desPrefix_eq_sum_range]
  rw [← Fin.sum_univ_eq_sum_range (fun j => desInd w j) K]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact wmi_desInd_eq_ite w j

theorem wmi_card_isMono_prefix {m K x : ℕ} (w : Fin K → Fin m) :
    Fintype.card { e : Fin K → Fin x // IsMono w e } =
      Nat.choose (x + K - (desPrefix w K + 1)) K := by
  rw [Fintype.card_congr (shiftEquiv w), wmi_card_monotone]
  by_cases hK : K = 0
  · subst K
    simp [desPrefix_zero]
  · by_cases hdx : desPrefix w K ≤ x
    · congr 1
      omega
    · have hleft : x - desPrefix w K + K - 1 < K := by omega
      have hright : x + K - (desPrefix w K + 1) < K := by omega
      rw [Nat.choose_eq_zero_of_lt hleft, Nat.choose_eq_zero_of_lt hright]

theorem wmi_card_isMono {m K x : ℕ} (w : Fin K → Fin m) :
    Fintype.card { e : Fin K → Fin x // IsMono w e } =
      Nat.choose
        (x + K - ((Finset.univ.filter (fun j : Fin K =>
          ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card + 1)) K := by
  rw [← wmi_desPrefix_eq_card w]
  exact wmi_card_isMono_prefix w

theorem wmi_pair_monotone_iff {m K x : ℕ}
    (w : Fin K → Fin m) (e : Fin K → Fin x) :
    Monotone (fun j => (toLex (e j, w j) : Fin x ×ₗ Fin m)) ↔ IsMono w e := by
  constructor
  · intro h
    constructor
    · intro a b hab
      rcases Prod.Lex.toLex_le_toLex.mp (h hab) with he | ⟨he, -⟩
      · exact he.le
      · exact he.le
    · intro j hj hw
      have hidx : j ≤ (⟨j.val + 1, hj⟩ : Fin K) := by
        change j.val ≤ j.val + 1
        omega
      rcases Prod.Lex.toLex_le_toLex.mp (h hidx) with he | ⟨-, hword⟩
      · exact he
      · exact False.elim (not_le_of_gt hw hword)
  · intro h
    cases K with
    | zero =>
        intro a
        exact Fin.elim0 a
    | succ n =>
        rw [Fin.monotone_iff_le_succ]
        intro j
        have hidx : j.castSucc ≤ j.succ := by
          rw [Fin.le_iff_val_le_val]
          simp
        have he := h.1 hidx
        apply Prod.Lex.toLex_le_toLex.mpr
        by_cases heq : e j.castSucc = e j.succ
        · right
          refine ⟨heq, ?_⟩
          by_contra hword
          have hgt : w j.castSucc > w j.succ := lt_of_not_ge hword
          have hstrict : e j.castSucc < e j.succ := by
            have hbound : (j.castSucc).val + 1 < n + 1 := by simp
            have hnext : (⟨(j.castSucc).val + 1, hbound⟩ : Fin (n + 1)) = j.succ :=
              Fin.ext (by simp)
            have hgt' : w j.castSucc > w ⟨(j.castSucc).val + 1, hbound⟩ := by
              rw [hnext]
              exact hgt
            have hs := h.2 j.castSucc hbound hgt'
            rw [hnext] at hs
            exact hs
          exact (ne_of_lt hstrict) heq
        · exact Or.inl (lt_of_le_of_ne he heq)

end MetaMathlibExt
end
