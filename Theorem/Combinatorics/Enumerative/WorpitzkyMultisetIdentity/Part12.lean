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
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part12


section

namespace MetaMathlibExt

theorem wmi_lhs_eq_word_sum (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
      ∑ w : { w : Fin (∑ i, k i) → Fin m //
          ∀ i, Fintype.card { j : Fin (∑ i, k i) // w j = i } = k i },
        Nat.choose
          (x + (∑ i, k i) -
            ((Finset.univ.filter (fun j : Fin (∑ i, k i) =>
              ∃ h : j.val + 1 < ∑ i, k i,
                w.1 j > w.1 ⟨j.val + 1, h⟩)).card + 1)) (∑ i, k i) := by
  rw [worpitzky_lhs_card]
  rw [Fintype.card_congr (wmiTupleWordEquiv m x k)]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro w _
  exact wmi_card_isMono w.1

theorem wmi_descent_succ_le_max {m K : ℕ} (w : Fin K → Fin m) :
    (Finset.univ.filter (fun j : Fin K =>
      ∃ h : j.val + 1 < K, w j > w ⟨j.val + 1, h⟩)).card + 1 ≤ max 1 K := by
  rw [← wmi_desPrefix_eq_card]
  by_cases hK : K = 0
  · subst K
    simp [desPrefix_zero]
  · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
    rw [desPrefix_last w hKpos]
    have hle := desPrefix_le_self w (K - 1)
    omega

end MetaMathlibExt
end
