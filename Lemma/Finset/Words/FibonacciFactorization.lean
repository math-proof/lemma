import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.FibonacciFactorization
open MetaMathlibExt


/--
[fibWord_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma fibWord_add_two_eq
  {n : ℕ} :
-- imply
  fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := by
-- proof
  apply MetaMathlibExt.fibWord_add_two n

/--
[fibWord_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma fibWord_factorization_eq
  {N : ℕ} :
-- imply
  false :: true :: (List.range N).flatMap fibWord = fibWord (N + 1) := by
-- proof
  apply MetaMathlibExt.fibWord_factorization N

/--
[fibWord_eq_ofFn_fibInf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma fibWord_eq_ofFn_fibInf_eq
  {n : ℕ} :
-- imply
  fibWord n = List.ofFn (fun i : Fin (fibWord n).length => fibInf i) := by
-- proof
  apply MetaMathlibExt.fibWord_eq_ofFn_fibInf n

/--
[fibInf_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma fibInf_factorization_eq
  :
-- imply
  (∀ N : ℕ,
    let w := by
-- proof
  apply MetaMathlibExt.fibInf_factorization

/--
[fibonacci_infinite_word_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/FibonacciFactorization.lean)
-/
@[path]
private lemma fibonacci_infinite_word_factorization_eq
  {f : ℕ → Fin 2}
  {fibWord : ℕ → List (Fin 2)}
-- given
  (h_one : fibWord 1 = [1])
  (h_two : fibWord 2 = [0])
  (h_rec : ∀ n : ℕ, fibWord (n + 3) = fibWord (n + 2) ++ fibWord (n + 1))
  (h_limit : ∀ n : ℕ, fibWord (n + 2) = List.ofFn (fun i : Fin (fibWord (n + 2)).length => f i)) :
-- imply
  (∀ N : ℕ,
    let w := by
-- proof
  apply MetaMathlibExt.fibonacci_infinite_word_factorization f fibWord h_one h_two h_rec h_limit


-- created on 2026-10-20
