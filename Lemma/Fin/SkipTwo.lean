import Mathlib
import sympy.Basic
import sympy.combinatorics.fin.SkipTwo


/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_injective_is
-- given
  (i j : Fin (n + 2))
  (hij : i < j) :
-- imply
  Function.Injective (Fin.skipTwo i j hij) := by
-- proof
  apply Fin.skipTwo_injective i j hij

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_strict_mono_is
-- given
  (i j : Fin (n + 2))
  (hij : i < j) :
-- imply
  StrictMono (Fin.skipTwo i j hij) := by
-- proof
  apply Fin.skipTwo_strictMono i j hij

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_inverse_is
-- given
  (i j x : Fin (n + 2))
  (hij : i < j)
  (hx_ne_i : x ≠ i)
  (hx_ne_j : x ≠ j) :
-- imply
  ∃ k : Fin n, Fin.skipTwo i j hij k = x := by
-- proof
  apply Fin.skipTwo_inverse i j hij x hx_ne_i hx_ne_j

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_range_eq
-- given
  (i j : Fin (n + 2))
  (hij : i < j) :
-- imply
  Set.range (Fin.skipTwo i j hij) = {x | x ≠ i ∧ x ≠ j} := by
-- proof
  apply Fin.skipTwo_range i j hij

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_ne_first_is
-- given
  (i j : Fin (n + 2))
  (hij : i < j)
  (k : Fin n) :
-- imply
  Fin.skipTwo i j hij k ≠ i := by
-- proof
  apply Fin.skipTwo_ne_first i j hij k

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_ne_second_is
-- given
  (i j : Fin (n + 2))
  (hij : i < j)
  (k : Fin n) :
-- imply
  Fin.skipTwo i j hij k ≠ j := by
-- proof
  apply Fin.skipTwo_ne_second i j hij k

/--
[SkipTwo](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Fin/SkipTwo.lean)
-/
@[path]
private lemma skip_two_mem_compl_is
-- given
  (i j : Fin (n + 2))
  (hij : i < j)
  (k : Fin n) :
-- imply
  Fin.skipTwo i j hij k ∈ ({i, j} : Finset (Fin (n + 2)))ᶜ := by
-- proof
  apply Fin.skipTwo_mem_compl i j hij k


-- created on 2026-10-11
