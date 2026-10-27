import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerCombinatorial
open Finset BigOperators Real ShannonEntropy ShearerCombinatorial LoomisWhitney


namespace ShearerCombinatorial

/--
[shannonEntropy_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean)
-/
@[path]
lemma shannonEntropy_uniform
  [Fintype α]
  [DecidableEq α]
  {F : Finset α}
-- given
  (hF : F.Nonempty) :
-- imply
  shannonEntropy (PMF.uniformOfFinset F hF) = Real.log F.card := by
-- proof
  simp only [shannonEntropy]
  have hcard_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hF)
  have hcard_ne : (F.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hval : ∀ s : α, (PMF.uniformOfFinset F hF s).toReal =
    if s ∈ F then (1 : ℝ) / F.card else 0 := by
    intro s
    split_ifs with h
    · rw [PMF.uniformOfFinset_apply, if_pos h]
      simp [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
    · rw [PMF.uniformOfFinset_apply, if_neg h]
      simp
  simp_rw [hval]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ F)]
  have h_out : ∑ s ∈ Finset.univ.filter (· ∉ F),
    Real.negMulLog (if s ∈ F then (1 : ℝ) / ↑F.card else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [if_neg hs, Real.negMulLog_zero]
  rw [h_out, add_zero]
  have h_in : ∀ s ∈ Finset.univ.filter (· ∈ F),
    Real.negMulLog (if s ∈ F then (1 : ℝ) / ↑F.card else 0) =
    Real.negMulLog (1 / F.card) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [if_pos hs]
  rw [Finset.sum_congr rfl h_in, Finset.sum_const]
  have hcard_filter : (Finset.univ.filter (· ∈ F)).card = F.card := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hcard_filter, nsmul_eq_mul]
  simp only [Real.negMulLog, one_div, Real.log_inv]
  field_simp

end ShearerCombinatorial

namespace ShearerCombinatorial

/--
[entropy_le_log_support_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean)
-/
@[path]
lemma entropy_le_log_support_card
  [Fintype S]
  [DecidableEq S]
  {p : PMF S} :
-- imply
  shannonEntropy p ≤ Real.log ((Finset.univ.filter (fun s => p s ≠ 0)).card) := by
-- proof
  set supp := Finset.univ.filter (fun s => p s ≠ 0) with supp_def
  have hsupp_ne : supp.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hzero : ∀ s : S, (p s).toReal = 0 := by
      intro s
      by_cases hs : p s = 0
      · simp [hs]
      · exfalso
        have : s ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩
        rw [h] at this; exact absurd this (Finset.notMem_empty _)
    have : ∑ s : S, (p s).toReal = 0 := by
      apply Finset.sum_eq_zero; intro s _; exact hzero s
    linarith [pmf_sum_toReal_eq_one p]
  have hn_pos : (0 : ℝ) < supp.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hsupp_ne)
  have hn_ne : (supp.card : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_split : shannonEntropy p = ∑ s ∈ supp, Real.negMulLog (p s).toReal := by
    simp only [shannonEntropy]
    symm
    apply Finset.sum_subset (Finset.subset_univ supp)
    intro s _ hs
    have : p s = 0 := by
      by_contra hne; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [this]
  have hsupp_sum : ∑ s ∈ supp, (p s).toReal = 1 := by
    have : ∑ s ∈ supp, (p s).toReal = ∑ s : S, (p s).toReal := by
      apply Finset.sum_subset (Finset.subset_univ supp)
      intro s _ hs
      have : p s = 0 := by
        by_contra hne; exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      simp [this]
    rw [this, pmf_sum_toReal_eq_one]
  rw [h_split]
  have hw_nn : ∀ i ∈ supp, (0 : ℝ) ≤ 1 / (supp.card : ℝ) :=
    fun _ _ => div_nonneg zero_le_one hn_pos.le
  have hw_sum : ∑ _ ∈ supp, (1 : ℝ) / (supp.card : ℝ) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]; field_simp
  have hmem : ∀ i ∈ supp, (p i).toReal ∈ Set.Ici (0 : ℝ) :=
    fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg
  have jensen := concaveOn_negMulLog.le_map_sum hw_nn hw_sum hmem
  simp only [smul_eq_mul] at jensen
  have lhs_eq : ∑ s ∈ supp, (1 : ℝ) / (supp.card : ℝ) * negMulLog (p s).toReal =
    (1 / (supp.card : ℝ)) * ∑ s ∈ supp, negMulLog (p s).toReal := (Finset.mul_sum ..).symm
  have rhs_sum : ∑ s ∈ supp, (1 : ℝ) / (supp.card : ℝ) * (p s).toReal =
    1 / (supp.card : ℝ) := by
    rw [← Finset.mul_sum, hsupp_sum, mul_one]
  rw [lhs_eq, rhs_sum] at jensen
  have h_le : ∑ s ∈ supp, negMulLog (p s).toReal ≤
    (supp.card : ℝ) * negMulLog (1 / (supp.card : ℝ)) := by
    have := mul_le_mul_of_nonneg_left jensen hn_pos.le
    rwa [← mul_assoc, mul_div_cancel₀ _ hn_ne, one_mul] at this
  have key : (supp.card : ℝ) * negMulLog (1 / (supp.card : ℝ)) =
    Real.log (supp.card : ℝ) := by
    simp [negMulLog]; field_simp
  linarith

end ShearerCombinatorial

namespace ShearerCombinatorial

/--
[entropy_map_uniform_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean)
-/
@[path]
lemma entropy_map_uniform_le
  [Fintype α]
  [Fintype β]
  [DecidableEq α]
  [DecidableEq β]
  {F : Finset α}
  {f : α → β}
-- given
  (hF : F.Nonempty) :
-- imply
  shannonEntropy ((PMF.uniformOfFinset F hF).map f) ≤ Real.log ((F.image f).card) := by
-- proof
  have hsupport_le : (Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card ≤
    (F.image f).card := by
    apply Finset.card_le_card
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [PMF.map_apply] at hb
    by_contra h_not_mem
    apply hb.2
    apply ENNReal.tsum_eq_zero.mpr
    intro a
    split_ifs with hab
    · rw [PMF.uniformOfFinset_apply, if_neg]
      intro ha
      exact h_not_mem (Finset.mem_image.mpr ⟨a, ha, hab.symm⟩)
    · rfl
  have hsupp_pos : (0 : ℝ) <
    (Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card := by
    apply Nat.cast_pos.mpr
    apply Finset.Nonempty.card_pos
    obtain ⟨a, ha⟩ := hF
    refine ⟨f a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [PMF.map_apply]
    intro heq
    have := ENNReal.tsum_eq_zero.mp heq a
    simp only [↓reduceIte] at this
    rw [PMF.uniformOfFinset_apply, if_pos ha] at this
    simp at this
  calc shannonEntropy ((PMF.uniformOfFinset F hF).map f)
    ≤ Real.log ((Finset.univ.filter (fun b => (PMF.uniformOfFinset F hF).map f b ≠ 0)).card) :=
      entropy_le_log_support_card _
    _ ≤ Real.log ((F.image f).card) := by
      apply Real.log_le_log hsupp_pos
      exact_mod_cast hsupport_le

end ShearerCombinatorial

namespace ShearerCombinatorial

/--
[shearer_set_family_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean)
-/
@[path]
lemma shearer_set_family_inequality
  {n s : ℕ}
  {F : Finset (Fin n → Bool)}
  {A : Fin s → Finset (Fin n)}
  {k : ℕ}
-- given
  (hcover : ShearerEntropy.CoveringCondition A k)
  (hF : F.Nonempty)
  (hk : 0 < k) :
-- imply
  (F.card : ℝ) ^ k ≤ ∏ j : Fin s, ((F.image (fun x (i : ↥(A j)) => x i.val)).card : ℝ) := by
-- proof
  set p := PMF.uniformOfFinset F hF
  have hH : shannonEntropy p = Real.log F.card := shannonEntropy_uniform F hF
  have hshearer := ShearerEntropy.shearer_entropy_inequality p A k hcover
  have hbound : ∀ j : Fin s,
    shannonEntropy (ShearerEntropy.marginal p (A j)) ≤
    Real.log ((F.image (fun x (i : ↥(A j)) => x i.val)).card) := by
    intro j
    show shannonEntropy (p.map (fun x (i : ↥(A j)) => x i.val)) ≤ _
    exact entropy_map_uniform_le F hF _
  have hlog : (k : ℝ) * Real.log F.card ≤
    ∑ j : Fin s, Real.log ((F.image (fun x (i : ↥(A j)) => x i.val)).card) := by
    calc (k : ℝ) * Real.log F.card
      = (k : ℝ) * shannonEntropy p := by rw [hH]
      _ ≤ ∑ j : Fin s, shannonEntropy (ShearerEntropy.marginal p (A j)) := hshearer
      _ ≤ ∑ j : Fin s, Real.log ((F.image (fun x (i : ↥(A j)) => x i.val)).card) :=
        Finset.sum_le_sum (fun j _ => hbound j)
  have hF_pos : (0 : ℝ) < F.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hF)
  have hπ_pos : ∀ j : Fin s, (0 : ℝ) < (F.image (fun x (i : ↥(A j)) => x i.val)).card := by
    intro j
    apply Nat.cast_pos.mpr
    exact Finset.Nonempty.card_pos (Finset.Nonempty.image hF _)
  have hne : ∀ j ∈ Finset.univ, ((F.image (fun x (i : ↥(A j)) => x i.val)).card : ℝ) ≠ 0 :=
    fun j _ => ne_of_gt (hπ_pos j)
  have h1 : Real.log ((F.card : ℝ) ^ k) ≤
    Real.log (∏ j : Fin s, ((F.image (fun x (i : ↥(A j)) => x i.val)).card : ℝ)) := by
    rwa [Real.log_pow, Real.log_prod hne]
  exact (Real.log_le_log_iff (pow_pos hF_pos k)
    (Finset.prod_pos (fun j _ => hπ_pos j))).mp h1
end ShearerCombinatorial
namespace LoomisWhitney
open Finset BigOperators Real ShannonEntropy


namespace LoomisWhitney

/--
[loomis_whitney_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean)
-/
@[path]
lemma loomis_whitney_inequality
  {n : ℕ}
  [Fintype α]
  [DecidableEq α]
  {S : Finset (Fin n → α)}
-- given
  (hne : S.Nonempty) :
-- imply
  S.card ^ (n - 1) ≤ ∏ i : Fin n, (S.image (coordProject i)).card := by
-- proof
  suffices h : (S.card : ℝ) ^ (n - 1) ≤
    ∏ i : Fin n, ((S.image (coordProject i)).card : ℝ) by exact_mod_cast h
  set p := PMF.uniformOfFinset S hne
  have hcover : ShearerEntropy.CoveringCondition (fun i : Fin n => Finset.univ.erase i) (n - 1) := by
    intro j
    have h1 : (Finset.univ.filter (fun i : Fin n => j ∈ Finset.univ.erase i)) =
      Finset.univ.erase j := by
      ext i; simp [Finset.mem_filter, Finset.mem_erase, ne_comm]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hshearer := ShearerEntropy.shearer_entropy_inequality p
    (fun i => Finset.univ.erase i) (n - 1) hcover
  have h_marginal_eq : ∀ i : Fin n,
    ShearerEntropy.marginal p (Finset.univ.erase i) = p.map (coordProject i) := by
    intro i; rfl
  simp_rw [h_marginal_eq] at hshearer
  have hH : shannonEntropy p = Real.log S.card :=
    ShearerCombinatorial.shannonEntropy_uniform S hne
  have hbound : ∀ i : Fin n,
    shannonEntropy (p.map (coordProject i)) ≤
    Real.log ((S.image (coordProject i)).card) :=
    fun i => ShearerCombinatorial.entropy_map_uniform_le S hne (coordProject i)
  have hlog : (↑(n - 1) : ℝ) * Real.log S.card ≤
    ∑ i : Fin n, Real.log ((S.image (coordProject i)).card) := by
    calc (↑(n - 1) : ℝ) * Real.log S.card
      = (↑(n - 1) : ℝ) * shannonEntropy p := by rw [hH]
      _ ≤ ∑ i : Fin n, shannonEntropy (p.map (coordProject i)) := hshearer
      _ ≤ ∑ i : Fin n, Real.log ((S.image (coordProject i)).card) :=
        Finset.sum_le_sum (fun i _ => hbound i)
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hne)
  have hπ_pos : ∀ i : Fin n, (0 : ℝ) < (S.image (coordProject i)).card :=
    fun i => Nat.cast_pos.mpr (Finset.Nonempty.card_pos (Finset.Nonempty.image hne _))
  have hne_log : ∀ i ∈ Finset.univ, ((S.image (coordProject i)).card : ℝ) ≠ 0 :=
    fun i _ => ne_of_gt (hπ_pos i)
  have h1 : Real.log ((S.card : ℝ) ^ (n - 1)) ≤
    Real.log (∏ i : Fin n, ((S.image (coordProject i)).card : ℝ)) := by
    rwa [Real.log_pow, Real.log_prod hne_log]
  exact (Real.log_le_log_iff (pow_pos hS_pos (n - 1))
    (Finset.prod_pos (fun i _ => hπ_pos i))).mp h1

end LoomisWhitney


-- created on 2026-10-23
