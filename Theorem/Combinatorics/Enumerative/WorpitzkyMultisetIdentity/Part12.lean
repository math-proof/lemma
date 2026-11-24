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
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part12


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
