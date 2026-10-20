import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.FibonacciWord
open MetaMathlibExt


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
[fibWord_nested_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibWord_nested_succ_eq
  :
-- imply
  ∀ (n : ℕ), ∃ t, fibWord (n + 1) = fibWord n ++ t
    | 0 => ⟨[true], rfl⟩
    | n + 1 => by
    obtain ⟨t, ht⟩ := by
-- proof
  apply MetaMathlibExt.fibWord_nested_succ

/--
[fibWord_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibWord_prefix_eq
  :
-- imply
  ∀ (n m : ℕ), n ≤ m → ∃ t, fibWord m = fibWord n ++ t
    | n, 0, h => by
    have hn : n = 0 := by
-- proof
  apply MetaMathlibExt.fibWord_prefix

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

/--
[fibWord_getD_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibWord_getD_eq_eq
  {n m k : ℕ}
-- given
  (hle : n ≤ m)
  (hk : k < (fibWord n).length) :
-- imply
  (fibWord m).getD k false = (fibWord n).getD k false := by
-- proof
  apply MetaMathlibExt.fibWord_getD_eq n m k hle hk

/--
[fibInf_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibInf_bound_eq
  {n : ℕ} :
-- imply
  n < (fibWord (n + 2)).length := by
-- proof
  apply MetaMathlibExt.fibInf_bound n

/--
[fibInf_agrees](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/FibonacciWord.lean)
-/
@[path]
private lemma fibInf_agrees_eq
  {m n : ℕ}
-- given
  (hm : n < (fibWord m).length) :
-- imply
  (fibWord m).getD n false = fibInf n := by
-- proof
  apply MetaMathlibExt.fibInf_agrees m n hm


-- created on 2026-10-20
