import Mathlib
import sympy.Basic
import Def.Data.Fin.SkipTwo


section
-- ac-theorems


namespace Fin

/-- `skipTwo` is injective. -/
lemma skipTwo_injective {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) :
    Function.Injective (skipTwo i j hij) := by
  intro a b hab
  simp only [skipTwo] at hab
  split_ifs at hab with h1 h2 h3 h4
  all_goals {
    simp only [Fin.ext_iff] at hab
    ext
    omega
  }

/-- `skipTwo` is strictly monotone. -/
lemma skipTwo_strictMono {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) :
    StrictMono (skipTwo i j hij) := by
  intro a b hab
  simp only [skipTwo]
  split_ifs with h1 h2 h3 h4 <;> simp only [Fin.lt_def] <;> omega

/-- Every element not equal to `i` or `j` is in the range of `skipTwo`.
    This is the key lemma for constructing the inverse of `skipTwo` on its range. -/
lemma skipTwo_inverse {n : ℕ} (i j : Fin (n + 2)) (hij : i < j)
    (x : Fin (n + 2)) (hx_ne_i : x ≠ i) (hx_ne_j : x ≠ j) :
    ∃ k : Fin n, skipTwo i j hij k = x := by
  by_cases h1 : (x : ℕ) < i
  · refine ⟨⟨x, by omega⟩, ?_⟩
    unfold skipTwo
    rw [ite_eq_left h1]
  · by_cases h2 : (x : ℕ) < j
    · -- x is between i and j (exclusive)
      have hx_gt_i : i < x := by
        push Not at h1
        exact lt_of_le_of_ne (Fin.le_def.mpr h1) (fun h => hx_ne_i h.symm)
      have hx_pos : 0 < x.val := by omega
      refine ⟨⟨x.val - 1, by omega⟩, ?_⟩
      unfold skipTwo
      have h1' : ¬((x.val - 1 : ℕ) < i) := by omega
      have h2' : (x.val - 1 : ℕ) + 1 < j := by omega
      simp only [h1', h2', ↓reduceIte, Fin.ext_iff]
      omega
    · -- x is after j
      push Not at h2
      have hx_gt_j : j < x := by
        apply lt_of_le_of_ne (Fin.le_def.mpr h2)
        intro heq
        exact hx_ne_j heq.symm
      refine ⟨⟨x.val - 2, by omega⟩, ?_⟩
      unfold skipTwo
      have h1' : ¬((x.val - 2 : ℕ) < i) := by omega
      have h2' : ¬((x.val - 2 : ℕ) + 1 < j) := by omega
      simp only [h1', h2', ↓reduceIte, Fin.ext_iff]
      omega

/-- The range of `skipTwo` is exactly the elements not equal to `i` or `j`. -/
lemma skipTwo_range {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) :
    Set.range (skipTwo i j hij) = {x | x ≠ i ∧ x ≠ j} := by
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · intro ⟨k, hk⟩
    subst hk
    simp only [skipTwo]
    split_ifs with h1 h2 <;> simp only [Fin.ne_iff_vne]
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega
  · intro ⟨hne_i, hne_j⟩
    exact skipTwo_inverse i j hij x hne_i hne_j

/-- `skipTwo` never returns its first skipped element. -/
lemma skipTwo_ne_first {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) (k : Fin n) :
    skipTwo i j hij k ≠ i := by
  have := skipTwo_range i j hij
  have hk_in_range : skipTwo i j hij k ∈ Set.range (skipTwo i j hij) := Set.mem_range_self k
  rw [this] at hk_in_range
  exact hk_in_range.1

/-- `skipTwo` never returns its second skipped element. -/
lemma skipTwo_ne_second {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) (k : Fin n) :
    skipTwo i j hij k ≠ j := by
  have := skipTwo_range i j hij
  have hk_in_range : skipTwo i j hij k ∈ Set.range (skipTwo i j hij) := Set.mem_range_self k
  rw [this] at hk_in_range
  exact hk_in_range.2

/-- `skipTwo` gives values in the complement of `{i, j}`. -/
lemma skipTwo_mem_compl {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) (k : Fin n) :
    skipTwo i j hij k ∈ ({i, j} : Finset (Fin (n + 2)))ᶜ := by
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨skipTwo_ne_first i j hij k, skipTwo_ne_second i j hij k⟩

end Fin
end


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
