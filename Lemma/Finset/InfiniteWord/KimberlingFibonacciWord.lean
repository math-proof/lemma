import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.KimberlingFibonacciWord
open MetaMathlibExt


/--
[kimberling_set_mod_two_fibonacci_word](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/KimberlingFibonacciWord.lean)
-/
@[path]
private lemma kimberling_set_mod_two_fibonacci_word_eq
  {K : Set ℕ}
  {S : ℕ → ℕ}
  {w : ℕ → Bool}
  {φ : List Bool → List Bool}
-- given
  (hK : K = { n | ∃ w : List Bool, w.foldl (fun x b => bif b then 4 * x - 1 else 2 * x) 1 = n })
  (hS : StrictMono S ∧ Set.range S = K)
  (hw : ∀ n, w n = decide (S (n + 1) % 2 = 1))
  (hφ : φ = List.flatMap (fun b => bif b then [false] else [false, true])) :
-- imply
  ∀ k : ℕ,
    List.ofFn (fun i : Fin (φ^[k] [false]).length => w ↑i) = φ^[k] [false] := by
-- proof
  apply MetaMathlibExt.kimberling_set_mod_two_fibonacci_word K hK S hS w hw φ hφ


-- created on 2026-10-20
