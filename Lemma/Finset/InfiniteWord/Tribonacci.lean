import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.Tribonacci
open InfiniteWord


/--
[tribonacciWordApprox_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_add_three_eq
  {n : Nat} :
-- imply
  tribonacciWordApprox (n + 3) =
    tribonacciWordApprox (n + 2) ++ tribonacciWordApprox (n + 1) ++
    tribonacciWordApprox n := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_add_three n

/--
[tribonacciWordApprox_length_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_length_add_three_eq
  {n : Nat} :
-- imply
  (tribonacciWordApprox (n + 3)).length =
    (tribonacciWordApprox (n + 2)).length +
    (tribonacciWordApprox (n + 1)).length + (tribonacciWordApprox n).length := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_length_add_three n

/--
[tribonacciWordApprox_length_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_length_ge_eq
  {n : Nat} :
-- imply
  n + 1 ≤ (tribonacciWordApprox n).length := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_length_ge n

/--
[tribonacciWordApprox_prefix_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_prefix_succ_eq
  :
-- imply
  ∀ n : Nat,
    List.IsPrefix (tribonacciWordApprox n) (tribonacciWordApprox (n + 1))
    | 0 => ⟨[.b], rfl⟩
    | 1 => ⟨[.a, .c], rfl⟩
    | n + 2 => by
    have hidx : n + 2 + 1 = n + 3 := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_prefix_succ

/--
[tribonacciWordApprox_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_prefix_eq
  {m n : Nat}
-- given
  (h : m ≤ n) :
-- imply
  List.IsPrefix (tribonacciWordApprox m) (tribonacciWordApprox n) := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_prefix h

/--
[tribonacciWordApprox_length_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWordApprox_length_mono_eq
  {m n : Nat}
-- given
  (h : m ≤ n) :
-- imply
  (tribonacciWordApprox m).length ≤ (tribonacciWordApprox n).length := by
-- proof
  apply InfiniteWord.tribonacciWordApprox_length_mono h

/--
[tribonacciWord_eq_getElem_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
private lemma tribonacciWord_eq_getElem_of_le_eq
  {k n : Nat}
-- given
  (hkn : k ≤ n)
  (hk : k < (tribonacciWordApprox n).length) :
-- imply
  (tribonacciWordApprox n)[k]'hk = tribonacciWord k := by
-- proof
  apply InfiniteWord.tribonacciWord_eq_getElem_of_le k n hkn hk


-- created on 2026-10-20
