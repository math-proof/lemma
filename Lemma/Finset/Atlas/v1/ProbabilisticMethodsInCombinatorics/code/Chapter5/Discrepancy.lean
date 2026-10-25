import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter5.Discrepancy
open Finset BigOperators Real Discrepancy


namespace Discrepancy

/--
[boolSign_not](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma boolSign_not
  {b : Bool} :
-- imply
  boolSign (!b) = -boolSign b := by
-- proof
  cases b <;> simp

end Discrepancy

namespace Discrepancy

/--
[disc_not](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma disc_not
  {n : ℕ}
  {f : Fin n → Bool}
  {S : Finset (Fin n)} :
-- imply
  disc (fun i => !(f i)) S = -disc f S := by
-- proof
  simp only [disc, boolSign_not, Finset.sum_neg_distrib]

end Discrepancy

namespace Discrepancy

/--
[exp_disc_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma exp_disc_eq_prod
  {n : ℕ}
  {s : ℝ}
  {S : Finset (Fin n)}
  {f : Fin n → Bool} :
-- imply
  exp (s * ↑(disc f S)) = ∏ i ∈ S, exp (s * ↑(boolSign (f i))) := by
-- proof
  simp only [disc, Int.cast_sum, Finset.mul_sum]
  exact exp_sum S (fun i => s * ↑(boolSign (f i)))

end Discrepancy

namespace Discrepancy

/--
[exp_moment_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma exp_moment_eq
  {n : ℕ}
  {s : ℝ}
  {S : Finset (Fin n)} :
-- imply
  ∑ f : Fin n → Bool, exp (s * ↑(disc f S)) = 2 ^ n * (cosh s) ^ S.card := by
-- proof
  simp_rw [exp_disc_eq_prod s S]
  conv_lhs =>
    arg 2; ext f
    rw [show (∏ i ∈ S, exp (s * ↑(boolSign (f i)))) =
      ∏ i : Fin n, if i ∈ S then exp (s * ↑(boolSign (f i))) else 1 from by
        conv_rhs => rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
        simp [Finset.filter_mem_eq_inter, Finset.prod_eq_one]]
  rw [Fintype.prod_sum (fun i b => if i ∈ S then exp (s * ↑(boolSign b)) else 1) |>.symm]
  simp_rw [show ∀ i : Fin n, (∑ j : Bool, if i ∈ S then exp (s * ↑(boolSign j)) else 1) =
    if i ∈ S then 2 * cosh s else 2 from fun i => by
      split_ifs with h
      · simp only [Fintype.sum_bool, boolSign_true, boolSign_false,
        Int.cast_one, Int.cast_neg, mul_one, mul_neg_one, cosh_eq]; ring
      · simp]
  conv_lhs =>
    arg 2; ext i
    rw [show (if i ∈ S then (2 : ℝ) * cosh s else 2) =
      (if i ∈ S then cosh s else 1) * 2 from by split_ifs <;> ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]; ring_nf; congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
  have h1 : ∀ x ∈ Finset.univ.filter (· ∈ S),
    (if x ∈ S then cosh s else (1 : ℝ)) = cosh s := by
    intro x hx; simp at hx; simp [hx]
  have h2 : ∀ x ∈ Finset.univ.filter (fun x => x ∉ S),
    (if x ∈ S then cosh s else (1 : ℝ)) = 1 := by
    intro x hx; simp at hx; simp [hx]
  rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2]
  simp [Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]

end Discrepancy

namespace Discrepancy

/--
[one_sided_chernoff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma one_sided_chernoff
  {n : ℕ}
  {S : Finset (Fin n)}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (ht : 0 < t) :
-- imply
  ((Finset.univ.filter (fun f : Fin n → Bool => t ≤ ↑(disc f S))).card : ℝ) ≤ 2 ^ n * exp (-(t ^ 2 / (2 * ↑n))) := by
-- proof
  set s := t / ↑n with hs_def
  have hs : 0 < s := div_pos ht (Nat.cast_pos.mpr hn)
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  have markov : ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ) * exp (s * t) ≤
    ∑ f : Fin n → Bool, exp (s * ↑(disc f S)) := by
    calc ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ) * exp (s * t)
      = ∑ f ∈ Finset.univ.filter (fun f => t ≤ ↑(disc f S)), exp (s * t) := by
        simp [mul_comm]
      _ ≤ ∑ f ∈ Finset.univ.filter (fun f => t ≤ ↑(disc f S)), exp (s * ↑(disc f S)) := by
        apply Finset.sum_le_sum; intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact exp_le_exp_of_le (mul_le_mul_of_nonneg_left hf hs.le)
      _ ≤ ∑ f, exp (s * ↑(disc f S)) :=
        Finset.sum_le_univ_sum_of_nonneg (fun f => (exp_pos _).le)
  rw [exp_moment_eq s S] at markov
  have hScard : S.card ≤ n :=
    S.card_le_univ.trans (by simp [Fintype.card_fin])
  have cosh_bound : (cosh s) ^ S.card ≤ exp (t ^ 2 / (2 * ↑n)) := by
    calc (cosh s) ^ S.card
      ≤ (exp (s ^ 2 / 2)) ^ S.card :=
        pow_le_pow_left₀ (cosh_pos s).le (cosh_le_exp_half_sq s) S.card
      _ = exp (↑S.card * (s ^ 2 / 2)) := (exp_nat_mul _ _).symm
      _ ≤ exp (↑n * (s ^ 2 / 2)) :=
        exp_le_exp_of_le (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hScard) (by positivity))
      _ = exp (t ^ 2 / (2 * ↑n)) := by congr 1; rw [hs_def]; field_simp
  have combined : ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ) * exp (s * t) ≤
    2 ^ n * exp (t ^ 2 / (2 * ↑n)) :=
    markov.trans (mul_le_mul_of_nonneg_left cosh_bound (by positivity))
  have hst : s * t = t ^ 2 / ↑n := by rw [hs_def]; field_simp
  rw [hst] at combined
  calc ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ)
    ≤ 2 ^ n * exp (t ^ 2 / (2 * ↑n)) / exp (t ^ 2 / ↑n) :=
      (le_div_iff₀ (exp_pos _)).mpr combined
    _ = 2 ^ n * (exp (t ^ 2 / (2 * ↑n)) / exp (t ^ 2 / ↑n)) := by ring
    _ = 2 ^ n * exp (t ^ 2 / (2 * ↑n) - t ^ 2 / ↑n) := by rw [← exp_sub]
    _ = 2 ^ n * exp (-(t ^ 2 / (2 * ↑n))) := by congr 1; field_simp; ring

end Discrepancy

namespace Discrepancy

/--
[card_filter_disc_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma card_filter_disc_neg
  {n : ℕ}
  {S : Finset (Fin n)}
  {t : ℝ} :
-- imply
  (Finset.univ.filter (fun f : Fin n → Bool => ↑(disc f S) ≤ -t)).card = (Finset.univ.filter (fun f : Fin n → Bool => t ≤ ↑(disc f S))).card := by
-- proof
  apply Finset.card_bij (fun f _ => fun i => !(f i))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rw [disc_not]; push_cast; linarith
  · intro f₁ _ f₂ _ h
    funext i; exact Bool.not_inj (congr_fun h i)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    refine ⟨fun i => !(f i), ?_, by funext i; simp⟩
    rw [disc_not]; push_cast; linarith

end Discrepancy

namespace Discrepancy

/--
[two_sided_chernoff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma two_sided_chernoff
  {n : ℕ}
  {S : Finset (Fin n)}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (ht : 0 < t) :
-- imply
  ((Finset.univ.filter (fun f : Fin n → Bool => t ≤ |↑(disc f S)|)).card : ℝ) ≤ 2 ^ (n + 1) * exp (-(t ^ 2 / (2 * ↑n))) := by
-- proof
  have hsplit : Finset.univ.filter (fun f : Fin n → Bool => t ≤ |↑(disc f S)|) ⊆
    (Finset.univ.filter (fun f => t ≤ ↑(disc f S))) ∪
    (Finset.univ.filter (fun f => ↑(disc f S) ≤ -t)) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hf ⊢
    exact (le_abs'.mp hf).symm
  have hcard :
    ((Finset.univ.filter (fun f : Fin n → Bool => t ≤ |↑(disc f S)|)).card : ℝ) ≤
    ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ) +
    ((Finset.univ.filter (fun f => ↑(disc f S) ≤ -t)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  rw [card_filter_disc_neg S t] at hcard
  have h1 := one_sided_chernoff hn S t ht
  calc _ ≤ 2 * ((Finset.univ.filter (fun f => t ≤ ↑(disc f S))).card : ℝ) := by linarith
    _ ≤ 2 * (2 ^ n * exp (-(t ^ 2 / (2 * ↑n)))) := by linarith
    _ = 2 ^ (n + 1) * exp (-(t ^ 2 / (2 * ↑n))) := by ring

end Discrepancy

namespace Discrepancy

/--
[mul_exp_neg_two_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma mul_exp_neg_two_log
  {m : ℕ}
-- given
  (hm : 0 < m) :
-- imply
  (↑m : ℝ) * exp (-(2 * log ↑m)) = 1 / ↑m := by
-- proof
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have h1 : exp (-(2 * log ↑m)) = ((↑m : ℝ) ^ 2)⁻¹ := by
    rw [exp_neg, show 2 * log (↑m : ℝ) = log ((↑m : ℝ) ^ 2) from by rw [log_pow]; ring,
      exp_log (by positivity)]
  rw [h1]; field_simp

end Discrepancy

namespace Discrepancy

/--
[discrepancy_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
lemma discrepancy_bound
  {n : ℕ}
  {F : Finset (Finset (Fin n))}
-- given
  (hn : 0 < n)
  (hF : 3 ≤ F.card) :
-- imply
  ∃ f : Fin n → Bool, ∀ S ∈ F, (|↑(disc f S)| : ℝ) ≤ 2 * sqrt (↑n * log ↑F.card) := by
-- proof
  set m := F.card with hm_def
  set t := 2 * sqrt (↑n * log ↑m) with ht_def
  have hm_pos : 0 < m := by omega
  have hm1 : (1 : ℝ) < ↑m := by exact_mod_cast show 1 < m by omega
  have hlog_pos : 0 < log ↑m := log_pos hm1
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have ht_sq : t ^ 2 / (2 * ↑n) = 2 * log ↑m := by
    rw [ht_def, mul_pow, sq_sqrt (by positivity : (0 : ℝ) ≤ ↑n * log ↑m)]
    field_simp
  let bad : (Fin n → Bool) → Prop := fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|
  have bad_subset : Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|) ⊆
    F.biUnion (fun S => Finset.univ.filter (fun f => t ≤ |↑(disc f S)|)) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hf ⊢
    obtain ⟨S, hS, hfS⟩ := hf
    exact ⟨S, hS, by simp [hfS]⟩
  have bad_card_bound :
    ((Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|)).card : ℝ)
    ≤ ↑m * (2 ^ (n + 1) * exp (-(2 * log ↑m))) := by
    calc ((Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|)).card : ℝ)
      ≤ ((F.biUnion (fun S => Finset.univ.filter (fun f => t ≤ |↑(disc f S)|))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card bad_subset
      _ ≤ ∑ S ∈ F, ((Finset.univ.filter (fun f => t ≤ |↑(disc f S)|)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ S ∈ F, (2 ^ (n + 1) * exp (-(t ^ 2 / (2 * ↑n)))) := by
        apply Finset.sum_le_sum
        intro S _
        exact two_sided_chernoff hn S t ht_pos
      _ = ↑m * (2 ^ (n + 1) * exp (-(t ^ 2 / (2 * ↑n)))) := by
        simp [Finset.sum_const, hm_def]
      _ = ↑m * (2 ^ (n + 1) * exp (-(2 * log ↑m))) := by
        rw [ht_sq]
  have bound_simplified :
    ↑m * (2 ^ (n + 1) * exp (-(2 * log ↑m))) = 2 ^ (n + 1) / ↑m := by
    rw [show ↑m * (2 ^ (n + 1) * exp (-(2 * log ↑m))) =
      2 ^ (n + 1) * (↑m * exp (-(2 * log ↑m))) from by ring]
    rw [mul_exp_neg_two_log m hm_pos]
    ring
  have total_bound :
    ((Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|)).card : ℝ)
    < 2 ^ n := by
    calc ((Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|)).card : ℝ)
      ≤ 2 ^ (n + 1) / ↑m := by rw [← bound_simplified]; exact bad_card_bound
      _ = 2 ^ n * (2 / ↑m) := by ring
      _ < 2 ^ n * 1 := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        rw [div_lt_one (by positivity : (0 : ℝ) < ↑m)]
        exact_mod_cast show 2 < m by omega
      _ = 2 ^ n := by ring
  have total_colorings : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have bad_lt_total :
    (Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|)).card <
    Fintype.card (Fin n → Bool) := by
    rw [total_colorings]
    exact_mod_cast total_bound
  have : ∃ f : Fin n → Bool, ¬(∃ S ∈ F, t ≤ |↑(disc f S)|) := by
    by_contra hall
    push Not at hall
    have : Finset.univ.filter (fun f => ∃ S ∈ F, t ≤ |↑(disc f S)|) = Finset.univ := by
      ext f; simp [hall f]
    rw [this, Finset.card_univ] at bad_lt_total
    exact lt_irrefl _ bad_lt_total
  obtain ⟨f, hf⟩ := this
  push Not at hf
  exact ⟨f, fun S hS => le_of_lt (hf S hS)⟩

end Discrepancy

/--
[boolSign_true](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
private lemma boolSign_true_eq :
-- imply
  boolSign true = 1 := by
-- proof
  apply Discrepancy.boolSign_true

/--
[boolSign_false](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Discrepancy.lean)
-/
@[path]
private lemma boolSign_false_eq :
-- imply
  boolSign false = -1 := by
-- proof
  apply Discrepancy.boolSign_false


-- created on 2026-10-23
