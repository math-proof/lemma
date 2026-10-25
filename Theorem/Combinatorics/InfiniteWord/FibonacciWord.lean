/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean -/

import Mathlib.Data.List.Defs
import Def.Combinatorics.InfiniteWord.FibonacciWord


namespace MetaMathlibExt

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

end MetaMathlibExt
