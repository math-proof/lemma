/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean -/

import Mathlib.Order.Monotone.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import sympy.atlas.Combinatorics.InfiniteWord.FibonacciWord
import Lemma.Finset.InfiniteWord.FibonacciWord
import Lemma.Finset.Words.FibonacciFactorization
import sympy.atlas.Combinatorics.Words.FibonacciFactorization
section
namespace MetaMathlibExt

/-! # Fibonacci word as self-generating set modulo 2
-/

private def kYStep : ℕ → Bool → ℕ := fun y b => bif b then 4 * y + 1 else 2 * y + 1
private def kWeight : List Bool → ℕ
  | [] => 0
  | b :: t => (bif b then 2 else 1) + kWeight t
private def kStep : ℕ → Bool → ℕ := fun x b => bif b then 4 * x - 1 else 2 * x
private def kVal : List Bool → ℕ := fun w => w.foldl kStep 1
private def kCodes : ℕ → List (List Bool)
  | 0 => [[]]
  | 1 => [[false]]
  | (n + 2) => (kCodes n).map (List.cons true) ++ (kCodes (n + 1)).map (List.cons false)

private theorem kY_affine : ∀ (l : List Bool) (y : ℕ),
    l.foldl kYStep y = 2 ^ (kWeight l) * y + l.foldl kYStep 0
  | [], y => by simp [kWeight]
  | b :: u, y => by
    have h1 := kY_affine u (kYStep y b)
    have h0 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep y b) = 2 ^ (kWeight (b :: u)) * y + u.foldl kYStep (kYStep 0 b)
    rw [h1, h0]
    cases b
    case true =>
      have hy : kYStep y true = 4 * y + 1 := rfl
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring
    case false =>
      have hy : kYStep y false = 2 * y + 1 := rfl
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hy, hz, hw, hp]
      ring

private theorem kR_lt : ∀ (w : List Bool), w.foldl kYStep 0 < 2 ^ (kWeight w)
  | [] => by simp [kWeight]
  | b :: u => by
    have ih := kR_lt u
    have h1 := kY_affine u (kYStep 0 b)
    change u.foldl kYStep (kYStep 0 b) < 2 ^ (kWeight (b :: u))
    rw [h1]
    cases b
    case true =>
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega
    case false =>
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hz, hw, hp]; omega

private theorem kFold_ge_one : ∀ (l : List Bool) (s : ℕ), 1 ≤ s → 1 ≤ l.foldl kStep s
  | [], s, hs => hs
  | b :: u, s, hs => by
    change 1 ≤ u.foldl kStep (kStep s b)
    exact kFold_ge_one u _ (kStep_ge_one hs b)

private theorem kFoldY_gen : ∀ (w : List Bool) (s : ℕ), 1 ≤ s →
    2 * (w.foldl kStep s) - 1 = 2 ^ (kWeight w) * (2 * s - 1) + w.foldl kYStep 0
  | [], s, _ => by simp [kWeight]
  | b :: u, s, hs => by
    have hs' : 1 ≤ kStep s b := kStep_ge_one hs b
    have h := kFoldY_gen u (kStep s b) hs'
    change 2 * (u.foldl kStep (kStep s b)) - 1
      = 2 ^ (kWeight (b :: u)) * (2 * s - 1) + u.foldl kYStep (kYStep 0 b)
    rw [h]
    have hR := kY_affine u (kYStep 0 b)
    rw [hR]
    cases b
    case true =>
      have e : kStep s true = 4 * s - 1 := rfl
      have hst : 2 * (kStep s true) - 1 = 4 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 true = 1 := rfl
      have hw : kWeight (true :: u) = 2 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (2 + kWeight u) = 4 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring
    case false =>
      have e : kStep s false = 2 * s := rfl
      have hst : 2 * (kStep s false) - 1 = 2 * (2 * s - 1) + 1 := by omega
      have hz : kYStep 0 false = 1 := rfl
      have hw : kWeight (false :: u) = 1 + kWeight u := rfl
      have hp : (2 : ℕ) ^ (1 + kWeight u) = 2 * 2 ^ kWeight u := by
        rw [pow_add]; norm_num
      rw [hst, hz, hw, hp]
      ring

private def kL (N : ℕ) : List (List Bool) := (List.range N).flatMap kCodes

private theorem kFirst_eq : ∀ (l : List ℕ) (S : ℕ → ℕ) (K : Set ℕ),
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

private theorem kFold_parity_congr : ∀ (a : List Bool) (s1 s2 : ℕ),
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

private def kParLev (m : ℕ) : List Bool := (kCodes m).map fun w => decide (kVal w % 2 = 1)

private theorem kMorph_conj : ∀ (s : List Bool),
    fibMorph s ++ [false] = [false] ++ (fibMorph s.reverse).reverse
  | [] => by rfl
  | b :: t => by
    have ih := kMorph_conj t
    cases b with
    | true =>
      have h1 : fibMorph (true :: t) = [false] ++ fibMorph t := rfl
      have eK : fibMorph [true] = [false] := rfl
      have eR : ([false] : List Bool).reverse = [false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false] ++ ·) ih
    | false =>
      have h1 : fibMorph (false :: t) = [false, true] ++ fibMorph t := rfl
      have eK : fibMorph [false] = [false, true] := rfl
      have eR : ([false, true] : List Bool).reverse = [true, false] := rfl
      rw [h1, List.reverse_cons, fibMorph_append, List.reverse_append, eK, eR]
      exact congrArg ([false, true] ++ ·) ih

private def kTail : ℕ → List Bool
  | 0 => [false, true]
  | 1 => [true, false]
  | (n + 2) => kTail n

private def kConcat : ℕ → List Bool
  | 0 => []
  | (n + 1) => kConcat n ++ (fibWord n).reverse

private theorem kConcat_tail : ∀ n, kConcat n ++ kTail n = fibWord (n + 1)
  | 0 => by rfl
  | (n + 1) => by
    have ih := kConcat_tail n
    have eC : kConcat (n + 1) = kConcat n ++ (fibWord n).reverse := rfl
    rw [eC, List.append_assoc, ← kSwap n, ← List.append_assoc, ih]
    exact (fibWord_add_two n).symm

private theorem kLPar_eq : ∀ N, ((kL N).map fun w => decide (kVal w % 2 = 1))
    = (List.range N).flatMap kParLev
  | 0 => by simp [kL]
  | N + 1 => by
    have ih := kLPar_eq N
    have eP : ((kCodes N).map fun w => decide (kVal w % 2 = 1)) = kParLev N := rfl
    have eS : List.flatMap kParLev [N] = kParLev N := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [kL_succ, List.range_succ, List.map_append, List.flatMap_append, ih, eP, eS]

private theorem kRangePar_eq : ∀ k,
    (List.range (k + 2)).flatMap kParLev = [true] ++ kConcat (k + 1)
  | 0 => by rfl
  | k + 1 => by
    change (List.range (k + 3)).flatMap kParLev = [true] ++ kConcat (k + 2)
    have ih := kRangePar_eq k
    have hr : List.range (k + 3) = List.range (k + 2) ++ [k + 2] := List.range_succ
    have eC : kConcat (k + 2) = kConcat (k + 1) ++ (fibWord (k + 1)).reverse := rfl
    have eR : kParLev (k + 2) = (fibWord (k + 1)).reverse := kParLev_eq (k + 1)
    have eS : List.flatMap kParLev [k + 2] = kParLev (k + 2) := by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hr, List.flatMap_append, ih, eS, eR, eC, List.append_assoc]
end MetaMathlibExt
end
