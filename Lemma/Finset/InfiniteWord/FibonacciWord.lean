import Mathlib
import sympy.Basic
import Theorem.Combinatorics.InfiniteWord.FibonacciWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[fibWord_nested_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
lemma fibWord_nested_succ
  :
-- imply
  ∀ (n : ℕ), ∃ t, fibWord (n + 1) = fibWord n ++ t
    | 0 => ⟨[true], rfl⟩
    | n + 1 => by
    obtain ⟨t, ht⟩ := by
-- proof
rw [ht]
  _ = fibMorph (fibWord n) ++ fibMorph t := fibMorph_append _ _
  _ = fibWord (n + 1) ++ fibMorph t := by
    rw [show fibMorph (fibWord n) = fibWord (n + 1) from rfl]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibWord_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
lemma fibWord_prefix
  :
-- imply
  ∀ (n m : ℕ), n ≤ m → ∃ t, fibWord m = fibWord n ++ t
    | n, 0, h => by
    have hn : n = 0 := by
-- proof
omega
  obtain ⟨t, ht⟩ := fibWord_prefix n m hle
  obtain ⟨s, hs⟩ := fibWord_nested_succ m
  exact ⟨t ++ s, by rw [hs, ht, List.append_assoc]⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibWord_getD_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
lemma fibWord_getD_eq
  {n m k : ℕ}
-- given
  (hle : n ≤ m)
  (hk : k < (fibWord n).length) :
-- imply
  (fibWord m).getD k false = (fibWord n).getD k false := by
-- proof
  obtain ⟨t, ht⟩ := fibWord_prefix n m hle
  rw [ht]
  exact getD_append_prefix (fibWord n) t k hk

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibInf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
lemma fibInf_bound
  {n : ℕ} :
-- imply
  n < (fibWord (n + 2)).length := by
-- proof
  have h := fibWord_length (n + 2)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fibInf_agrees](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
lemma fibInf_agrees
  {m n : ℕ}
-- given
  (hm : n < (fibWord m).length) :
-- imply
  (fibWord m).getD n false = fibInf n := by
-- proof
  unfold fibInf
  have hlen : n < (fibWord (n + 2)).length := fibInf_bound n
  let k := Nat.max m (n + 2)
  have hmk : m ≤ k := Nat.le_max_left m (n + 2)
  have hnk : n + 2 ≤ k := Nat.le_max_right m (n + 2)
  have h1 : (fibWord k).getD n false = (fibWord m).getD n false :=
    fibWord_getD_eq m k n hmk hm
  have h2 : (fibWord k).getD n false = (fibWord (n + 2)).getD n false :=
    fibWord_getD_eq (n + 2) k n hnk hlen
  rwa [← h1]

end MetaMathlibExt

/--
[fibMorph_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibMorph_append_eq
  :
-- imply
  ∀ (a b : List Bool), fibMorph (a ++ b) = fibMorph a ++ fibMorph b
    | [], b => by simp [fibMorph]
    | x :: xs, b => by simp [fibMorph, fibMorph_append xs b, List.append_assoc]
    /-- Every letter maps to a nonempty word, so the morphism never shrinks length.
    Concept `jis_sem_f409ef3715730614fd194b4d`. -/
    private lemma  fibMorph_length_ge : ∀ (w : List Bool), w.length ≤ (fibMorph w).length
    | [] => by simp [fibMorph]
    | false :: w => by
    have ih := by
-- proof
  apply MetaMathlibExt.fibMorph_append

/--
[fibMorph_length_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibMorph_length_ge_eq
  :
-- imply
  ∀ (w : List Bool), w.length ≤ (fibMorph w).length
    | [] => by simp [fibMorph]
    | false :: w => by
    have ih := by
-- proof
  apply MetaMathlibExt.fibMorph_length_ge

/--
[fibWord_head](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibWord_head_eq
  :
-- imply
  ∀ (n : ℕ), ∃ t, fibWord n = false :: t
    | 0 => ⟨[], rfl⟩
    | n + 1 => by
    obtain ⟨t, ht⟩ := by
-- proof
  apply MetaMathlibExt.fibWord_head

/--
[fibWord_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibWord_length_eq
  :
-- imply
  ∀ (n : ℕ), n + 1 ≤ (fibWord n).length
    | 0 => by simp [fibWord]
    | n + 1 => by
    have ih := by
-- proof
  apply MetaMathlibExt.fibWord_length

/--
[getD_append_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma getD_append_prefix_eq
  :
-- imply
  ∀ (a t : List Bool) (k : ℕ),
    k < a.length → (a ++ t).getD k false = a.getD k false
    | [], _, _, hk => by simp at hk
    | _ :: _, _, 0, _ => by simp
    | x :: xs, t, k + 1, hk => by
    have hk' : k < xs.length := by
-- proof
  apply MetaMathlibExt.getD_append_prefix


-- created on 2026-10-20
-- updated on 2026-10-23
