/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean -/

import Mathlib.Data.List.Defs

namespace MetaMathlibExt

/-- Binary Fibonacci substitution on letters, `0` maps to `01` and `1` maps to `0`.
Letters `0` and `1` are represented by `false` and `true`.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibSubst : Bool → List Bool
  | false => [false, true]
  | true => [false]

/-- Extension of the Fibonacci substitution to finite words by concatenation.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibMorph : List Bool → List Bool
  | [] => []
  | b :: w => fibSubst b ++ fibMorph w

/-- Finite Fibonacci iterates starting at the one-letter word `0`.
The source displays `0`, `01`, `010`, `01001`, `01001010`, and so on.
Concept `jis_sem_f409ef3715730614fd194b4d`, source `jis_2ff564e576beedc024b95b9a`. -/
def fibWord : ℕ → List Bool
  | 0 => [false]
  | n + 1 => fibMorph (fibWord n)

/-- One-sided infinite Fibonacci word as the pointwise limit of the nested
finite iterates. Index `n` is read from the finite iterate at depth `n + 2`.
Concept `jis_sem_f409ef3715730614fd194b4d`, sources `jis_138e7e26819c0bf6a015b5e7`,
`jis_52830047049fa91220ac91eb`, `jis_2ff564e576beedc024b95b9a`. -/
def fibInf (n : ℕ) : Bool :=
  (fibWord (n + 2)).getD n false

/-- The Fibonacci morphism distributes over concatenation.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibMorph_append : ∀ (a b : List Bool), fibMorph (a ++ b) = fibMorph a ++ fibMorph b
  | [], b => by simp [fibMorph]
  | x :: xs, b => by simp [fibMorph, fibMorph_append xs b, List.append_assoc]

/-- Every letter maps to a nonempty word, so the morphism never shrinks length.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibMorph_length_ge : ∀ (w : List Bool), w.length ≤ (fibMorph w).length
  | [] => by simp [fibMorph]
  | false :: w => by
    have ih := fibMorph_length_ge w
    simp [fibMorph, fibSubst]
    omega
  | true :: w => by
    have ih := fibMorph_length_ge w
    simp [fibMorph, fibSubst]
    omega

/-- Every finite iterate begins with the letter `0`.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_head : ∀ (n : ℕ), ∃ t, fibWord n = false :: t
  | 0 => ⟨[], rfl⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := fibWord_head n
    exact ⟨true :: fibMorph t, by simp [fibWord, ht, fibMorph, fibSubst]⟩

/-- Finite iterates grow long enough to cover every index: `n + 1 ≤ length`.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_length : ∀ (n : ℕ), n + 1 ≤ (fibWord n).length
  | 0 => by simp [fibWord]
  | n + 1 => by
    have ih := fibWord_length n
    obtain ⟨t, ht⟩ := fibWord_head n
    have hge := fibMorph_length_ge t
    have htlen : (fibWord n).length = t.length + 1 := by simp [ht]
    have hlen : (fibWord (n + 1)).length = 2 + (fibMorph t).length := by
      simp [fibWord, ht, fibMorph, fibSubst]
      omega
    omega

/-- Successive finite iterates are nested.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_nested_succ : ∀ (n : ℕ), ∃ t, fibWord (n + 1) = fibWord n ++ t
  | 0 => ⟨[true], rfl⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := fibWord_nested_succ n
    refine ⟨fibMorph t, ?_⟩
    calc fibWord (n + 1 + 1) = fibMorph (fibWord (n + 1)) := rfl
      _ = fibMorph (fibWord n ++ t) := by rw [ht]
      _ = fibMorph (fibWord n) ++ fibMorph t := fibMorph_append _ _
      _ = fibWord (n + 1) ++ fibMorph t := by
        rw [show fibMorph (fibWord n) = fibWord (n + 1) from rfl]

/-- Finite iterates are nested: earlier words are prefixes of later words.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_prefix : ∀ (n m : ℕ), n ≤ m → ∃ t, fibWord m = fibWord n ++ t
  | n, 0, h => by
    have hn : n = 0 := by omega
    subst hn
    exact ⟨[], by simp⟩
  | n, m + 1, h => by
    by_cases hn : n = m + 1
    · subst hn
      exact ⟨[], by simp⟩
    · have hle : n ≤ m := by omega
      obtain ⟨t, ht⟩ := fibWord_prefix n m hle
      obtain ⟨s, hs⟩ := fibWord_nested_succ m
      exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩

/-- Reading an index below the prefix length through an appended suffix agrees.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem getD_append_prefix : ∀ (a t : List Bool) (k : ℕ),
    k < a.length → (a ++ t).getD k false = a.getD k false
  | [], _, _, hk => by simp at hk
  | _ :: _, _, 0, _ => by simp
  | x :: xs, t, k + 1, hk => by
    have hk' : k < xs.length := by simpa using hk
    have ih := getD_append_prefix xs t k hk'
    simpa using ih

/-- Covered indices stabilize across iterates: later words agree with earlier ones.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibWord_getD_eq (n m k : ℕ) (hle : n ≤ m) (hk : k < (fibWord n).length) :
    (fibWord m).getD k false = (fibWord n).getD k false := by
  obtain ⟨t, ht⟩ := fibWord_prefix n m hle
  rw [ht]
  exact getD_append_prefix (fibWord n) t k hk

/-- The chosen iteration depth `n + 2` always covers index `n`.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibInf_bound (n : ℕ) : n < (fibWord (n + 2)).length := by
  have h := fibWord_length (n + 2)
  omega

/-- Every covered index of every finite iterate agrees with the infinite word.
Concept `jis_sem_f409ef3715730614fd194b4d`. -/
theorem fibInf_agrees (m n : ℕ) (hm : n < (fibWord m).length) :
    (fibWord m).getD n false = fibInf n := by
  unfold fibInf
  have hlen : n < (fibWord (n + 2)).length := fibInf_bound n
  let k := Nat.max m (n + 2)
  have hmk : m ≤ k := Nat.le_max_left m (n + 2)
  have hnk : n + 2 ≤ k := Nat.le_max_right m (n + 2)
  have h1 : (fibWord k).getD n false = (fibWord m).getD n false :=
    fibWord_getD_eq m k n hmk hm
  have h2 : (fibWord k).getD n false = (fibWord (n + 2)).getD n false :=
    fibWord_getD_eq (n + 2) k n hnk hlen
  rw [← h1]
  exact h2

end MetaMathlibExt
