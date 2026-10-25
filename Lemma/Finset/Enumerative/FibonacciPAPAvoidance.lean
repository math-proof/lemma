import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.FibonacciPAPAvoidance.Part5
open MetaMathlibExt


namespace MetaMathlibExt

/--
[frontPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma frontPerm_apply {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π)
  (i : Fin (π (Fin.last N)).val) (hlt : i.val < N + 1) :
  (frontPerm π h i).val = (π ⟨i.val, hlt⟩).val :=
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[frontPerm_good](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma frontPerm_good {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
  IsGood (π (Fin.last N)).val (frontPerm π h) := by
  have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  obtain ⟨hpar, h312, h231⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hlt : i.val < N + 1 := by have := i.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ i hlt]
    exact hpar ⟨i.val, hlt⟩
  · intro i j k hij hjk ⟨hjk', hki'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ j hlj, frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk]
      at hjk'
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk, frontPerm_apply π ⟨hpar, h312, h231⟩ i hli]
      at hki'
    exact h312 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hjk', hki'⟩
  · intro i j k hij hjk ⟨hki', hij'⟩
    have hli : i.val < N + 1 := by have := i.isLt; omega
    have hlj : j.val < N + 1 := by have := j.isLt; omega
    have hlk : k.val < N + 1 := by have := k.isLt; omega
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ k hlk, frontPerm_apply π ⟨hpar, h312, h231⟩ i hli]
      at hki'
    rw [frontPerm_apply π ⟨hpar, h312, h231⟩ i hli, frontPerm_apply π ⟨hpar, h312, h231⟩ j hlj]
      at hij'
    exact h231 ⟨i.val, hli⟩ ⟨j.val, hlj⟩ ⟨k.val, hlk⟩ hij hjk ⟨hki', hij'⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[parity_c](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma parity_c {N : ℕ} (π : Equiv.Perm (Fin (N + 1))) (h : IsGood (N + 1) π) :
  (N - (π (Fin.last N)).val) % 2 = 0 := by
  obtain ⟨hpar, _, _⟩ := h
  have hp := hpar (Fin.last N)
  have hlast : (Fin.last N).val = N := Fin.val_last N
  have hcN : (π (Fin.last N)).val ≤ N := Nat.lt_succ_iff.mp (Fin.is_lt _)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[range_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma range_sum {N : ℕ} :
  Fintype.card {π : Equiv.Perm (Fin (N+1)) // IsGood (N+1) π} =
    ∑ b ∈ (Finset.range (N+1)).filter (fun b => (N - b) % 2 = 0),
      Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := by
  classical
  rw [Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise
      (f := fun π => (π (Fin.last N)).val) (t := Finset.range (N+1))
      (fun π _ => Finset.mem_range.mpr (π (Fin.last N)).isLt),
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.mem_range] at hv
  rw [Finset.filter_filter]
  by_cases hpar : (N - v) % 2 = 0
  · rw [ite_eq_left hpar, ← Fintype.card_subtype
    (fun π => IsGood (N+1) π ∧ (π (Fin.last N)).val = v)]
    apply Fintype.card_congr
    refine (Equiv.subtypeEquivRight ?_).trans (fiberEquiv ⟨v, hv⟩ hpar)
    intro π
    constructor
    · rintro ⟨hg, hval⟩; exact ⟨hg, Fin.ext hval⟩
    · rintro ⟨hg, heq⟩; exact ⟨hg, by rw [heq]⟩
  · rw [ite_eq_right hpar, ← Fintype.card_subtype
    (fun π => IsGood (N+1) π ∧ (π (Fin.last N)).val = v),
    Fintype.card_eq_zero_iff]
    refine ⟨fun π => ?_⟩
    obtain ⟨hg, hval⟩ := π.2
    have hpc := parity_c π.1 hg
    rw [hval] at hpc
    exact hpar hpc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma recurrence (m : ℕ) :
  Fintype.card {π : Equiv.Perm (Fin (m+3)) // IsGood (m+3) π} =
    Fintype.card {σ : Equiv.Perm (Fin (m+2)) // IsGood (m+2) σ} +
    Fintype.card {τ : Equiv.Perm (Fin (m+1)) // IsGood (m+1) τ} := by
  have e1 : Fintype.card {π : Equiv.Perm (Fin (m+3)) // IsGood (m+3) π} =
    ∑ b ∈ (Finset.range (m+3)).filter (fun b => (m + 2 - b) % 2 = 0),
      Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := range_sum (N := m+2)
  have e2 : Fintype.card {τ : Equiv.Perm (Fin (m+1)) // IsGood (m+1) τ} =
    ∑ b ∈ (Finset.range (m+1)).filter (fun b => (m - b) % 2 = 0),
      Fintype.card {ρ : Equiv.Perm (Fin b) // IsGood b ρ} := range_sum (N := m)
  have hset : (Finset.range (m+2)).filter (fun b => (m + 2 - b) % 2 = 0)
    = (Finset.range (m+1)).filter (fun b => (m - b) % 2 = 0) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [e1, e2, Finset.range_add_one, Finset.filter_insert,
    ite_eq_left (show (m + 2 - (m + 2)) % 2 = 0 by omega),
    Finset.sum_insert (by simp [Finset.mem_filter, Finset.mem_range]), hset]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_isGood_eq_fib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
private lemma card_isGood_eq_fib : ∀ n, 1 ≤ n →
  Fintype.card {π : Equiv.Perm (Fin n) // IsGood n π} = Nat.fib n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    match n, hn with
    | 1, _ => decide
    | 2, _ => decide
    | (m+3), _ =>
      rw [recurrence m, IH (m+2) (by omega) (by omega), IH (m+1) (by omega) (by omega)]
      have h : Nat.fib (m+3) = Nat.fib (m+1) + Nat.fib (m+2) := Nat.fib_add_two (n := m+1)
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibonacci_card_parity_alternating_avoiding_312_231](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FibonacciPAPAvoidance.lean)
-/
@[path]
lemma fibonacci_card_parity_alternating_avoiding_312_231
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Fintype.card { π : Equiv.Perm (Fin n) //
    (∀ i, (π i).val % 2 = i.val % 2) ∧
    (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π j).val < (π k).val ∧ (π k).val < (π i).val)) ∧
    (∀ i j k : Fin n, i.val < j.val → j.val < k.val →
    ¬ ((π k).val < (π i).val ∧ (π i).val < (π j).val)) } = Nat.fib n := by
-- proof
  exact card_isGood_eq_fib n hn

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
