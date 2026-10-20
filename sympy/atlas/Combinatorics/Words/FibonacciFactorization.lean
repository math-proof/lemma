/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean -/

import Mathlib.Data.List.Basic
import sympy.atlas.Combinatorics.InfiniteWord.FibonacciWord
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.RelClasses

namespace MetaMathlibExt

/-- The finite Fibonacci words satisfy the concatenation recurrence
`fibWord (n + 2) = fibWord (n + 1) ++ fibWord n`. -/
theorem fibWord_add_two (n : ℕ) : fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change fibMorph (fibWord (n + 2)) = fibMorph (fibWord (n + 1)) ++ fibMorph (fibWord n)
    rw [ih, fibMorph_append]

/-- Prepending `01` to the concatenation `fibWord 0 ++ ⋯ ++ fibWord (N - 1)` gives
`fibWord (N + 1)`. -/
theorem fibWord_factorization (N : ℕ) :
    false :: true :: (List.range N).flatMap fibWord = fibWord (N + 1) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.cons_append,
      ← List.cons_append, ih, fibWord_add_two]

/-- Every finite Fibonacci word lists the first letters of the infinite Fibonacci word. -/
theorem fibWord_eq_ofFn_fibInf (n : ℕ) :
    fibWord n = List.ofFn (fun i : Fin (fibWord n).length => fibInf i) := by
  refine List.ext_getElem (by simp) fun i h _ => ?_
  rw [List.getElem_ofFn, ← fibInf_agrees n i h]
  simp [h]

private lemma ofFn_prefix_of_le {α : Type*} (g : ℕ → α) {k m : ℕ} (hkm : k ≤ m) :
    List.ofFn (fun i : Fin k => g i) <+: List.ofFn (fun i : Fin m => g i) := by
  rw [List.prefix_iff_getElem]
  exact ⟨by simpa using hkm, fun i hi => by simp⟩

/-- Factorization of the infinite Fibonacci word as `0 · 1 · fibWord 0 · fibWord 1 ⋯`: each
partial product is a prefix of `fibInf`, and every prefix of `fibInf` lies in one of them.
Source: Gabriele Fici, "Factorizations of the Fibonacci Infinite Word", Journal of Integer
Sequences 18 (2015), Article 15.9.3, equation `fibo`. -/
theorem fibInf_factorization :
    (∀ N : ℕ,
      let w := false :: true :: (List.range N).flatMap fibWord
      w = List.ofFn (fun i : Fin w.length => fibInf i)) ∧
    ∀ k : ℕ, ∃ N : ℕ,
      List.ofFn (fun i : Fin k => fibInf i) <+:
        false :: true :: (List.range N).flatMap fibWord := by
  refine ⟨fun N => ?_, fun k => ⟨k, ?_⟩⟩
  · change false :: true :: (List.range N).flatMap fibWord = List.ofFn
      (fun i : Fin (false :: true :: (List.range N).flatMap fibWord).length => fibInf i)
    rw [fibWord_factorization]
    exact fibWord_eq_ofFn_fibInf (N + 1)
  · rw [fibWord_factorization, fibWord_eq_ofFn_fibInf (k + 1)]
    have := fibWord_length (k + 1)
    exact ofFn_prefix_of_le fibInf (by omega)

private lemma fibWord_bridge (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ n : ℕ, F (n + 2) = (fibWord n).map (fun b => cond b 1 0)
  | 0 => by simp [h_two, fibWord]
  | 1 => by rw [h_rec 0, h_two, h_one]; rfl
  | n + 2 => by
    rw [show n + 2 + 2 = (n + 1) + 3 by omega, h_rec (n + 1),
      fibWord_bridge F h_one h_two h_rec (n + 1), show n + 1 + 1 = n + 2 by omega,
      fibWord_bridge F h_one h_two h_rec n, fibWord_add_two, List.map_append]

private lemma fibWord_concat_eq (F : ℕ → List (Fin 2))
    (h_one : F 1 = [1]) (h_two : F 2 = [0])
    (h_rec : ∀ n : ℕ, F (n + 3) = F (n + 2) ++ F (n + 1)) :
    ∀ N : ℕ, (0 :: (List.range N).flatMap (fun n => F (n + 1))) = F (N + 2)
  | 0 => by simp [h_two]
  | N + 1 => by
    have hb : ∀ n : ℕ, F (n + 1 + 1) = (fibWord n).map (fun b => cond b 1 0) :=
      fibWord_bridge F h_one h_two h_rec
    rw [fibWord_bridge F h_one h_two h_rec (N + 1), ← fibWord_factorization,
      List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [hb, h_one, List.map_flatMap]

/--
The Fibonacci infinite word is obtained by concatenating `0` with the finite Fibonacci words.
Source: Gabriele Fici, "Factorizations of the Fibonacci Infinite Word", Journal of Integer
Sequences 18 (2015), Article 15.9.3, Proposition lines 188-195 (equation `fibo`),
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Fici/fici5.tex>.

Proves `Wanted` entry `fibonacci_infinite_word_factorization`.
-/
theorem fibonacci_infinite_word_factorization
    (f : ℕ → Fin 2)
    (fibWord : ℕ → List (Fin 2))
    (h_one : fibWord 1 = [1])
    (h_two : fibWord 2 = [0])
    (h_rec : ∀ n : ℕ, fibWord (n + 3) = fibWord (n + 2) ++ fibWord (n + 1))
    (h_limit : ∀ n : ℕ,
      fibWord (n + 2) =
        List.ofFn (fun i : Fin (fibWord (n + 2)).length => f i)) :
    (∀ N : ℕ,
      let w := 0 :: (List.range N).flatMap (fun n => fibWord (n + 1))
      w = List.ofFn (fun i : Fin w.length => f i)) ∧
    ∀ k : ℕ, ∃ N : ℕ,
      List.IsPrefix
        (List.ofFn (fun i : Fin k => f i))
        (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) := by
  have heq : ∀ N : ℕ,
      (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) = fibWord (N + 2) :=
    fibWord_concat_eq fibWord h_one h_two h_rec
  refine ⟨?_, fun k => ⟨k, ?_⟩⟩
  · intro N
    change (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))) =
      List.ofFn (fun i : Fin (0 :: (List.range N).flatMap (fun n => fibWord (n + 1))).length => f i)
    rw [heq N]
    exact h_limit N
  · have hlen : k ≤ (fibWord (k + 2)).length := by
      rw [fibWord_bridge fibWord h_one h_two h_rec k, List.length_map]
      have := fibWord_length k
      omega
    rw [heq k, h_limit k]
    exact ofFn_prefix_of_le f hlen

end MetaMathlibExt
