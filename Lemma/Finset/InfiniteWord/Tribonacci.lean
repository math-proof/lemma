import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.Tribonacci
open InfiniteWord


namespace InfiniteWord

/--
[tribonacciWordApprox_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
lemma tribonacciWordApprox_prefix
  {m n : Nat}
-- given
  (h : m ≤ n) :
-- imply
  List.IsPrefix (tribonacciWordApprox m) (tribonacciWordApprox n) := by
-- proof
  have hadd : ∀ d : Nat,
    List.IsPrefix (tribonacciWordApprox m) (tribonacciWordApprox (m + d)) := by
    intro d
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨[], List.append_nil _⟩
    | succ d ih =>
      have hidx : m + (d + 1) = (m + d) + 1 := by omega
      rw [hidx]
      obtain ⟨t, ht⟩ := ih
      obtain ⟨s, hs⟩ := tribonacciWordApprox_prefix_succ (m + d)
      exact ⟨t ++ s, by rw [← List.append_assoc, ht, hs]⟩
  have hidx : m + (n - m) = n := by omega
  rw [← hidx]
  exact hadd (n - m)

end InfiniteWord

namespace InfiniteWord

/--
[tribonacciWordApprox_length_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
lemma tribonacciWordApprox_length_mono
  {m n : Nat}
-- given
  (h : m ≤ n) :
-- imply
  (tribonacciWordApprox m).length ≤ (tribonacciWordApprox n).length :=
-- proof
  (tribonacciWordApprox_prefix h).length_le

end InfiniteWord

namespace InfiniteWord

/--
[tribonacciWord_eq_getElem_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/Tribonacci.lean)
-/
@[path]
lemma tribonacciWord_eq_getElem_of_le
  {k n : Nat}
-- given
  (hkn : k ≤ n)
  (hk : k < (tribonacciWordApprox n).length) :
-- imply
  (tribonacciWordApprox n)[k]'hk = tribonacciWord k := by
-- proof
  unfold tribonacciWord
  exact ((tribonacciWordApprox_prefix hkn).getElem (by
    have h := tribonacciWordApprox_length_ge k
    omega)).symm

end InfiniteWord

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


-- created on 2026-10-20
-- updated on 2026-10-23
