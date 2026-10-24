import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.DistinctSums
open DubroffFoxXu DistinctSumsBound
open Finset
open Finset BigOperators
open Finset BigOperators Classical


namespace DubroffFoxXu

/--
[boolToFinset_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma boolToFinset_injective
  {k : ℕ} :
-- imply
  Function.Injective (@boolToFinset k) := by
-- proof
  intro ε₁ ε₂ h
  funext i
  have hmem : (i ∈ boolToFinset ε₁) ↔ (i ∈ boolToFinset ε₂) := by rw [h]
  simp only [boolToFinset, mem_filter, mem_univ, true_and] at hmem
  cases h₁ : ε₁ i <;> cases h₂ : ε₂ i <;> simp_all

end DubroffFoxXu

namespace DubroffFoxXu

/--
[weightedSum_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma weightedSum_eq_sum
  {k : ℕ}
  {x : Fin k → ℕ}
  {ε : Fin k → Bool} :
-- imply
  weightedSum x ε = ∑ i ∈ boolToFinset ε, x i := by
-- proof
  unfold weightedSum boolToFinset
  rw [Finset.sum_filter]

end DubroffFoxXu

namespace DubroffFoxXu

/--
[weightedSum_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma weightedSum_injective
  {k : ℕ}
  {x : Fin k → ℕ}
-- given
  (hdist : HasDistinctSubsetSumsFin x) :
-- imply
  Function.Injective (weightedSum x) := by
-- proof
  intro ε₁ ε₂ h
  have h1 : ∑ i ∈ boolToFinset ε₁, x i = ∑ i ∈ boolToFinset ε₂, x i := by
    rw [← weightedSum_eq_sum, ← weightedSum_eq_sum, h]
  exact boolToFinset_injective (hdist h1)

end DubroffFoxXu

namespace DubroffFoxXu

/--
[weightedSum_add_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma weightedSum_add_compl
  {k : ℕ}
  {x : Fin k → ℕ}
  {ε : Fin k → Bool} :
-- imply
  weightedSum x ε + weightedSum x (boolCompl ε) = ∑ i : Fin k, x i := by
-- proof
  unfold weightedSum boolCompl
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases ε i <;> simp

end DubroffFoxXu

namespace DubroffFoxXu

/--
[weightedSum_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma weightedSum_neighbor
  {k : ℕ}
  {x : Fin k → ℕ}
  {ε u : Fin k → Bool}
  {i : Fin k}
-- given
  (hagree : ∀ j : Fin k, j ≠ i → ε j = u j)
  (hε_true : ε i = true)
  (hu_false : u i = false) :
-- imply
  weightedSum x ε = weightedSum x u + x i := by
-- proof
  unfold weightedSum
  have heq_rest : ∀ j ∈ Finset.univ.erase i, (if ε j = true then x j else 0) =
    (if u j = true then x j else 0) := fun j hj => by
    rw [Finset.mem_erase] at hj; rw [hagree j hj.1]
  have lhs : (∑ j : Fin k, if ε j = true then x j else 0) =
    x i + ∑ j ∈ Finset.univ.erase i, (if ε j = true then x j else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hε_true]
  have rhs : (∑ j : Fin k, if u j = true then x j else 0) =
    0 + ∑ j ∈ Finset.univ.erase i, (if u j = true then x j else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [hu_false]
  rw [lhs, rhs]
  have := Finset.sum_congr rfl heq_rest
  omega
/-- Harper's vertex-isoperimetric inequality on the hypercube (Theorem 4.6.4), variant
  using `cubeBoundary`: any subset $A$ of half-size in $\{0,1\}^k$ has vertex
  boundary at least $\binom{k}{\lfloor k/2 \rfloor}$. -/
end DubroffFoxXu
namespace DistinctSumsBound
open Finset BigOperators Classical


namespace DistinctSumsBound

/--
[sum_boolSign_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma sum_boolSign_prod
  {k : ℕ}
  {l m : Fin k} :
-- imply
  ∑ ε : Fin k → Bool, boolSign (ε l) * boolSign (ε m) = if l = m then (2 ^ k : ℤ) else 0 := by
-- proof
  split_ifs with h
  · subst h
    have hh : ∀ ε : Fin k → Bool, boolSign (ε l) * boolSign (ε l) = 1 := by
      intro ε; simp [boolSign]; cases ε l <;> simp
    simp only [hh, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp
  · apply Finset.sum_involution (fun (ε : Fin k → Bool) _ => Function.update ε l (!ε l))
    · intro ε _
      have hne : Function.update ε l (!ε l) m = ε m :=
        Function.update_of_ne (Ne.symm h) _ _
      simp only [boolSign, Function.update_self, hne]
      cases ε l <;> cases ε m <;> simp
    · intro ε _ _ heq
      have := congr_fun heq l; simp [Function.update] at this
    · intro _ _; exact Finset.mem_univ _
    · intro ε _; funext j; simp only [Function.update]
      split_ifs with h1
      · subst h1; simp
      · rfl

end DistinctSumsBound

namespace DistinctSumsBound

/--
[variance_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma variance_identity
  {k : ℕ}
  {x : Fin k → ℤ} :
-- imply
  ∑ ε : Fin k → Bool, (∑ l : Fin k, boolSign (ε l) * x l) ^ 2 = 2 ^ k * ∑ l : Fin k, x l ^ 2 := by
-- proof
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext l; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext l; arg 2; ext m; arg 2; ext ε
    rw [show boolSign (ε l) * x l * (boolSign (ε m) * x m) =
      x l * x m * (boolSign (ε l) * boolSign (ε m)) from by ring]
  simp_rw [← Finset.mul_sum, sum_boolSign_prod]
  conv_lhs =>
    arg 2; ext l; arg 2; ext m
    rw [show x l * x m * (if l = m then (2 : ℤ) ^ k else 0) =
      if l = m then x l * x m * 2 ^ k else 0 from by split_ifs <;> ring]
  simp_rw [Finset.sum_ite_eq, mem_univ, if_true]
  rw [Finset.mul_sum]; congr 1; ext l; ring

end DistinctSumsBound

namespace DistinctSumsBound

/--
[two_ws_minus_S_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma two_ws_minus_S_eq
  {k : ℕ}
  {x : Fin k → ℕ}
  {ε : Fin k → Bool} :
-- imply
  (2 * (DubroffFoxXu.weightedSum x ε : ℤ) - (∑ i : Fin k, (x i : ℤ))) = ∑ i : Fin k, boolSign (ε i) * (x i : ℤ) := by
-- proof
  simp only [DubroffFoxXu.weightedSum, boolSign]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1; ext i; cases ε i <;> simp; ring

end DistinctSumsBound

namespace DistinctSumsBound

/--
[distinct_sums_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/DistinctSums.lean)
-/
@[path]
lemma distinct_sums_bound
  {k n : ℕ}
  {x : Fin k → ℕ}
-- given
  (hk : 0 < k)
  (hn : 0 < n)
  (hx_pos : ∀ i, 0 < x i)
  (hx_le : ∀ i, x i ≤ n)
  (hdist : DubroffFoxXu.HasDistinctSubsetSumsFin x) :
-- imply
  3 * 2 ^ k ≤ 8 * n * (Nat.sqrt k + 1) := by
-- proof
  set ws := DubroffFoxXu.weightedSum x
  set S := ∑ i : Fin k, x i
  set T := 2 * n * (Nat.sqrt k + 1) with hT_def
  set inside : Finset (Fin k → Bool) :=
    Finset.univ.filter (fun ε => ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs < T)
  set outside : Finset (Fin k → Bool) :=
    Finset.univ.filter (fun ε => T ≤ ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs)
  have hpart : inside.card + outside.card = 2 ^ k := by
    have h_union : inside ∪ outside = Finset.univ := by
      ext ε; simp only [inside, outside, mem_union, mem_filter, mem_univ, true_and, iff_true]
      exact Nat.lt_or_ge _ _
    have h_disj : Disjoint inside outside := by
      simp only [inside, outside]; rw [Finset.disjoint_filter]; intro _ _ h1 h2; omega
    rw [← Finset.card_union_of_disjoint h_disj, h_union,
      Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hvar : ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - (S : ℤ)) ^ 2 =
    (2 ^ k : ℤ) * ∑ i : Fin k, (x i : ℤ) ^ 2 := by
    have heq : ∀ ε, (2 * (ws ε : ℤ) - (S : ℤ)) =
      (2 * (DubroffFoxXu.weightedSum x ε : ℤ) - ∑ i, (x i : ℤ)) := by
      intro ε; simp [ws, S]
    simp_rw [heq, two_ws_minus_S_eq]
    exact variance_identity k (fun i => (x i : ℤ))
  have houtside_bound : outside.card * 4 ≤ 2 ^ k := by
    have hvar_ub : (outside.card : ℤ) * (4 * (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) ≤
      (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) := by
      have h_lower : ∀ ε ∈ outside, (T : ℤ) ^ 2 ≤ ((2 * (ws ε : ℤ) - S) ^ 2) := by
        intro ε hε
        have hmem : T ≤ ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs := by
          simp only [outside, mem_filter, mem_univ, true_and] at hε; exact hε
        nlinarith [sq_abs (2 * (ws ε : ℤ) - S),
          show (T : ℤ) ≤ |2 * (ws ε : ℤ) - S| from by
            rw [Int.abs_eq_natAbs]; exact_mod_cast hmem]
      have h_markov : (outside.card : ℤ) * (T : ℤ) ^ 2 ≤
        ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - S) ^ 2 := by
        calc (outside.card : ℤ) * (T : ℤ) ^ 2
          = ∑ _ ∈ outside, (T : ℤ) ^ 2 := by rw [Finset.sum_const]; push_cast; ring
          _ ≤ ∑ ε ∈ outside, ((2 * (ws ε : ℤ)) - S) ^ 2 := Finset.sum_le_sum h_lower
          _ ≤ ∑ ε : Fin k → Bool, ((2 * (ws ε : ℤ)) - S) ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
      have hsum_sq : (∑ i : Fin k, (x i : ℤ) ^ 2) ≤ (k : ℤ) * (n : ℤ) ^ 2 := by
        calc ∑ i : Fin k, (x i : ℤ) ^ 2
          ≤ ∑ _ : Fin k, (n : ℤ) ^ 2 := by
            apply Finset.sum_le_sum; intro i _
            exact sq_le_sq' (by linarith [show (0 : ℤ) ≤ x i from by positivity])
              (by exact_mod_cast hx_le i)
          _ = k * (n : ℤ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; push_cast; ring
      have hT_sq : (T : ℤ) ^ 2 = 4 * (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 := by
        simp only [hT_def]; push_cast; ring
      nlinarith [h_markov, hvar, hsum_sq]
    suffices h : (outside.card : ℤ) * 4 ≤ (2 ^ k : ℤ) from by exact_mod_cast h
    by_contra h_neg; push_neg at h_neg
    have hk_lt : (k : ℤ) < ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 := by
      push_cast; exact_mod_cast Nat.lt_succ_sqrt' k
    have step1 : (2 ^ k : ℤ) * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) <
      (outside.card : ℤ) * 4 * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) := by
      nlinarith [show (0 : ℤ) < (n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2 from by positivity]
    have step2 : (outside.card : ℤ) * 4 * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) ≤
      (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) := by nlinarith [hvar_ub]
    have step3 : (2 ^ k : ℤ) * ((k : ℤ) * (n : ℤ) ^ 2) <
      (2 ^ k : ℤ) * ((n : ℤ) ^ 2 * ((Nat.sqrt k + 1 : ℕ) : ℤ) ^ 2) := by
      nlinarith [show (0 : ℤ) < (2 ^ k : ℤ) * (n : ℤ) ^ 2 from by positivity, hk_lt]
    linarith
  have hinside_le : inside.card ≤ T := by
    have hinj := DubroffFoxXu.weightedSum_injective hdist
    suffices h : (inside.image ws).card ≤ T by
      rwa [Finset.card_image_of_injOn (hinj.injOn.mono (fun _ _ => trivial))] at h
    set hi := (S + T + 1) / 2
    set lo := hi - T
    apply le_trans (Finset.card_le_card _)
      (by rw [Nat.card_Ico]; omega : (Finset.Ico lo hi).card ≤ T)
    intro a ha
    rw [Finset.mem_image] at ha; obtain ⟨ε, hε, rfl⟩ := ha
    have habs : ((2 * (ws ε : ℤ)) - (S : ℤ)).natAbs < T := by
      simp only [inside, mem_filter, mem_univ, true_and] at hε; exact hε
    rw [Finset.mem_Ico]; constructor <;> omega
  have hinside_ge : 3 * 2 ^ k ≤ 4 * inside.card := by omega
  have h_final : 4 * inside.card ≤ 4 * T := by omega
  have hT_expand : 4 * T = 8 * n * (Nat.sqrt k + 1) := by
    show 4 * (2 * n * (Nat.sqrt k + 1)) = 8 * n * (Nat.sqrt k + 1); ring
  linarith

end DistinctSumsBound


-- created on 2026-10-23
