import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CompositionsTribonacci
open MetaMathlibExt


namespace MetaMathlibExt

/--
[compositionsTrib_fixed_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_fixed_succ (k n : ℕ) :
  compositionsTrib_fixed (k + 1) (n + 3) =
    compositionsTrib_fixed k (n + 2) + compositionsTrib_fixed k (n + 1) +
      compositionsTrib_fixed k n := by
  unfold compositionsTrib_fixed
  rw [Fintype.card_congr (compositionsTrib_consEquiv k (n + 3))]
  rw [Fintype.card_sigma]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Nat.reduceAdd, add_zero]
  have h1 :
    Fintype.card {b : Fin k → Fin 3 //
      (∑ i : Fin k, ((b i).val + 1)) + 1 = n + 3} =
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) = n + 2} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  have h2 :
    Fintype.card {b : Fin k → Fin 3 //
      (∑ i : Fin k, ((b i).val + 1)) + 2 = n + 3} =
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) = n + 1} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  have h3 :
    Fintype.card {b : Fin k → Fin 3 //
      (∑ i : Fin k, ((b i).val + 1)) + 3 = n + 3} =
      Fintype.card {b : Fin k → Fin 3 //
        (∑ i : Fin k, ((b i).val + 1)) = n} := by
    exact Fintype.card_congr <| Equiv.subtypeEquivRight fun _ ↦ by omega
  rw [h1, h2, h3]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_length_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_length_le_sum {k : ℕ} (a : Fin k → Fin 3) :
  k ≤ ∑ i : Fin k, ((a i).val + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_succ]
    have htail := ih (Fin.tail a)
    simp only [Fin.tail] at htail
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_fixed_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_fixed_eq_zero {k n : ℕ} (h : n < k) :
  compositionsTrib_fixed k n = 0 := by
  unfold compositionsTrib_fixed
  let hEmpty : IsEmpty {a : Fin k → Fin 3 //
    (∑ i : Fin k, ((a i).val + 1)) = n} :=
    ⟨fun a ↦ by
      have hle := compositionsTrib_length_le_sum a.1
      have ha := a.2
      omega⟩
  exact @Fintype.card_eq_zero _ inferInstance hEmpty

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_fixed_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_fixed_zero {n : ℕ} (h : 0 < n) :
  compositionsTrib_fixed 0 n = 0 := by
  simp [compositionsTrib_fixed, h.ne]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_count_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_count_add_three (n : ℕ) :
  compositionsTrib_count (n + 3) =
    compositionsTrib_count (n + 2) + compositionsTrib_count (n + 1) +
      compositionsTrib_count n := by
  have hdrop1 :
    (∑ k ∈ Finset.range (n + 3), compositionsTrib_fixed k (n + 1)) =
      ∑ k ∈ Finset.range (n + 2), compositionsTrib_fixed k (n + 1) := by
    rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
  have hdrop2 :
    (∑ k ∈ Finset.range (n + 3), compositionsTrib_fixed k n) =
      ∑ k ∈ Finset.range (n + 1), compositionsTrib_fixed k n := by
    rw [show n + 3 = (n + 2) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    rw [compositionsTrib_fixed_eq_zero (by omega), add_zero]
  unfold compositionsTrib_count
  conv_lhs => rw [Finset.sum_range_succ']
  rw [compositionsTrib_fixed_zero (n := n + 3) (by omega), add_zero]
  simp_rw [compositionsTrib_fixed_succ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hdrop1, hdrop2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_count_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_count_one : compositionsTrib_count 1 = 1 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_count_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_count_two : compositionsTrib_count 2 = 2 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_count_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_count_three : compositionsTrib_count 3 = 4 := by
  decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositionsTrib_count_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositionsTrib_count_eq
  (T : ℕ → ℕ)
  (hT1 : T 1 = 1)
  (hT2 : T 2 = 1)
  (hT3 : T 3 = 2)
  (hTrec : ∀ m : ℕ, 3 < m →
    T m = T (m - 1) + T (m - 2) + T (m - 3)) :
  ∀ n : ℕ, 0 < n → compositionsTrib_count n = T (n + 1) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  by_cases hsmall : n < 4
  · have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    obtain rfl | rfl | rfl := hcases
    · rw [compositionsTrib_count_one, hT2]
    · rw [compositionsTrib_count_two, hT3]
    · have hT4 : T 4 = 4 := by
      rw [hTrec 4 (by omega), hT3, hT2, hT1]
      rw [compositionsTrib_count_three, hT4]
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn4
    have hm3 := ih (m + 3) (by omega) (by omega)
    have hm2 := ih (m + 2) (by omega) (by omega)
    have hm1 := ih (m + 1) (by omega) (by omega)
    rw [show 4 + m = (m + 1) + 3 by omega, compositionsTrib_count_add_three]
    rw [hm3, hm2, hm1]
    have hrec := hTrec (m + 5) (by omega)
    have hsub1 : m + 5 - 1 = m + 4 := by omega
    have hsub2 : m + 5 - 2 = m + 3 := by omega
    have hsub3 : m + 5 - 3 = m + 2 := by omega
    rw [hsub1, hsub2, hsub3] at hrec
    have hindex : (m + 1 + 3) + 1 = m + 5 := by omega
    rw [hindex, hrec]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositions_parts_one_two_three_eq_tribonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
lemma compositions_parts_one_two_three_eq_tribonacci
  {n : ℕ}
  {T : ℕ → ℕ}
-- given
  (hn : 0 < n)
  (hT1 : T 1 = 1)
  (hT2 : T 2 = 1)
  (hT3 : T 3 = 2)
  (hTrec : ∀ m : ℕ, 3 < m → T m = T (m - 1) + T (m - 2) + T (m - 3)) :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    Fintype.card {a : Fin k → Fin 3 //
    (∑ i : Fin k, ((a i).val + 1)) = n}) =
    T (n + 1) := by
-- proof
  change compositionsTrib_count n = T (n + 1)
  exact compositionsTrib_count_eq T hT1 hT2 hT3 hTrec n hn

end MetaMathlibExt

namespace MetaMathlibExt

/--
[compositions_parts_one_two_three_eq_canonical_tribonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
lemma compositions_parts_one_two_three_eq_canonical_tribonacci
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    Fintype.card {a : Fin k → Fin 3 //
    (∑ i : Fin k, ((a i).val + 1)) = n}) =
    tribonacci (n + 2) := by
-- proof
  exact compositions_parts_one_two_three_eq_tribonacci n hn
    (fun k ↦ tribonacci (k + 1)) (by rfl) (by rfl) (by rfl) (by
      intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ m by omega)
      rw [show 4 + k + 1 = (k + 2) + 3 by omega]
      rw [show 4 + k - 1 + 1 = k + 4 by omega]
      rw [show 4 + k - 2 + 1 = k + 3 by omega]
      rw [show 4 + k - 3 + 1 = k + 2 by omega]
      rfl)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
