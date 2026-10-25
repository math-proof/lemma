/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/

import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.InfiniteWord.FibonacciWord
import Lemma.Finset.InfiniteWord.FibonacciWord
import Lemma.Finset.Words.FibonacciFactorization
import Theorem.Combinatorics.Words.FibonacciFactorization
import Def.Combinatorics.InfiniteWord.KimberlingFibonacciWord.Part2


section

namespace MetaMathlibExt

theorem kFirst_eq : ∀ (l : List ℕ) (S : ℕ → ℕ) (K : Set ℕ),
    StrictMono S → Set.range S = K →
    l.Pairwise (· < ·) → (∀ x ∈ l, x ∈ K) →
    (∀ x ∈ l, ∀ y ∈ K, y ∉ l → x < y) →
    ∀ (i : ℕ) (hi : i < l.length), S i = l[i]'hi
  | [], S, K, hS, hK, _, _, _ => fun i hi => by simp at hi
  | a :: t, S, K, hS, hK, hsorted, hmem, hbelow => fun i hi => by
    have hsorted_t : t.Pairwise (· < ·) := (List.pairwise_cons.mp hsorted).2
    have hleast : ∀ x ∈ t, a < x := (List.pairwise_cons.mp hsorted).1
    have haK : a ∈ K := hmem a ((List.mem_cons).mpr (Or.inl rfl))
    have hmin : ∀ y ∈ K, S 0 ≤ y := by
      intro y hy
      rw [← hK] at hy
      obtain ⟨n, rfl⟩ := hy
      cases n with
      | zero => exact le_rfl
      | succ n => exact le_of_lt (hS (Nat.zero_lt_succ n))
    have hS0 : S 0 = a := by
      have hS0K : S 0 ∈ K := by
        rw [← hK]
        exact ⟨0, rfl⟩
      have hle : S 0 ≤ a := hmin a haK
      by_contra hne
      have hmemST : S 0 ∈ a :: t := by
        by_contra hnotin
        have hlt := hbelow a ((List.mem_cons).mpr (Or.inl rfl)) (S 0) hS0K hnotin
        omega
      cases List.mem_cons.mp hmemST with
      | inl h => exact hne h
      | inr h =>
        have hlt := hleast (S 0) h
        omega
    have hS1 : StrictMono (fun n => S (n + 1)) := by
      intro x y hxy
      change S (x + 1) < S (y + 1)
      exact hS (by omega)
    have hK1 : Set.range (fun n => S (n + 1)) = { y ∈ K | y ≠ a } := by
      ext y
      constructor
      · rintro ⟨n, hn⟩
        have hn' : S (n + 1) = y := hn
        subst hn'
        constructor
        · rw [← hK]
          exact ⟨n + 1, rfl⟩
        · intro hy
          have hlt : S 0 < S (n + 1) := hS (Nat.zero_lt_succ n)
          omega
      · rintro ⟨hyK, hnea⟩
        rw [← hK] at hyK
        obtain ⟨n, rfl⟩ := hyK
        cases n with
        | zero => exact (hnea hS0).elim
        | succ n => exact ⟨n, rfl⟩
    have hmem_t : ∀ x ∈ t, x ∈ { y ∈ K | y ≠ a } := by
      intro x hx
      have hxK := hmem x ((List.mem_cons).mpr (Or.inr hx))
      have hne : x ≠ a := by
        intro heq
        have hlt := hleast x hx
        omega
      exact ⟨hxK, hne⟩
    have hbelow_t : ∀ x ∈ t, ∀ y ∈ { y ∈ K | y ≠ a }, y ∉ t → x < y := by
      intro x hx y hyK hyt
      obtain ⟨hyK', hne⟩ := hyK
      have hynot : y ∉ a :: t := by
        intro hc
        cases List.mem_cons.mp hc with
        | inl he => exact hne he
        | inr ht => exact hyt ht
      exact hbelow x ((List.mem_cons).mpr (Or.inr hx)) y hyK' hynot
    have ih := kFirst_eq t (fun n => S (n + 1)) { y ∈ K | y ≠ a } hS1 hK1
      hsorted_t hmem_t hbelow_t
    cases i with
    | zero => simpa using hS0
    | succ i =>
      have hlen : (a :: t).length = t.length + 1 := rfl
      have hti : i < t.length := by omega
      have h := ih i hti
      simpa using h

theorem kFold_parity_congr : ∀ (a : List Bool) (s1 s2 : ℕ),
    1 ≤ s1 → 1 ≤ s2 → s1 % 2 = s2 % 2 →
    (a.foldl kStep s1) % 2 = (a.foldl kStep s2) % 2
  | [], s1, s2, _, _, h => h
  | b :: t, s1, s2, h1, h2, h => by
    change (t.foldl kStep (kStep s1 b)) % 2 = (t.foldl kStep (kStep s2 b)) % 2
    apply kFold_parity_congr
    · exact kStep_ge_one h1 b
    · exact kStep_ge_one h2 b
    · cases b with
      | true =>
        have e1 : kStep s1 true = 4 * s1 - 1 := rfl
        have e2 : kStep s2 true = 4 * s2 - 1 := rfl
        omega
      | false =>
        have e1 : kStep s1 false = 2 * s1 := rfl
        have e2 : kStep s2 false = 2 * s2 := rfl
        omega

end MetaMathlibExt
end
