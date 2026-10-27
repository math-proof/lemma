import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
open Finset Real SparseVarshamovGilbert


namespace SparseVarshamovGilbert

/--
[sparsevec_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparsevec_card
  {d k : ℕ} :
-- imply
  Fintype.card (SparseVec d k) = Nat.choose d k := by
-- proof
  have : Fintype.card (SparseVec d k) = Fintype.card {S : Finset (Fin d) // S.card = k} := by
    apply Fintype.card_congr
    refine Equiv.subtypeEquiv
      { toFun := fun (f : Fin d → Bool) => Finset.univ.filter (fun i => f i = true)
        invFun := fun (S : Finset (Fin d)) => fun i => decide (i ∈ S)
        left_inv := by
          intro f; ext i
          simp [Finset.mem_filter]
        right_inv := by
          intro S; ext i
          simp } ?_
    intro f
    simp only [Equiv.coe_fn_mk, l0norm]
  rw [this, Fintype.card_finset_len, Fintype.card_fin]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[hammingDist_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma hammingDist_comm
  {d : ℕ}
  {f g : Fin d → Bool} :
-- imply
  hammingDist f g = hammingDist g f := by
-- proof
  unfold hammingDist; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ne_comm

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[greedy_packing_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma greedy_packing_bound
  {α : Type}
  [Fintype α]
  [DecidableEq α]
  {ball : α → Finset α}
  {B : ℕ}
-- given
  (ball_self : ∀ x, x ∈ ball x)
  (ball_symm : ∀ x y, y ∈ ball x → x ∈ ball y)
  (ball_bound : ∀ x, (ball x).card ≤ B) :
-- imply
  ∃ T : Finset α, Fintype.card α ≤ T.card * B ∧ (∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∉ ball x) := by
-- proof
  classical
  let packings := Finset.univ.powerset.filter (fun T : Finset α =>
    ∀ x ∈ T, ∀ y ∈ T, x ≠ y → y ∉ ball x)
  have hfin : packings.Nonempty := ⟨∅, by simp [packings, Finset.mem_filter]⟩
  obtain ⟨T, hT_mem, hT_max⟩ := packings.exists_max_image Finset.card hfin
  have hT_pack := (Finset.mem_filter.mp hT_mem).2
  have hcover : ∀ z, ∃ t ∈ T, z ∈ ball t := by
    intro z
    by_cases hz : z ∈ T
    · exact ⟨z, hz, ball_self z⟩
    ·
      by_contra habs
      push Not at habs
      have : ∀ x ∈ T.cons z hz, ∀ y ∈ T.cons z hz, x ≠ y → y ∉ ball x := by
        intro x hx y hy hne
        simp only [Finset.mem_cons] at hx hy
        obtain rfl | hx <;> rcases hy with rfl | hy := hx
        · exact absurd rfl hne
        · intro hball; exact habs y hy (ball_symm _ _ hball)
        · intro hball; exact habs x hx hball
        · exact hT_pack x hx y hy hne
      linarith [hT_max (T.cons z hz)
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), this⟩),
        Finset.card_cons hz]
  refine ⟨T, ?_, hT_pack⟩
  calc Fintype.card α = Finset.univ.card := Finset.card_univ.symm
    _ ≤ (T.biUnion ball).card :=
      Finset.card_le_card (fun z _ => Finset.mem_biUnion.mpr (hcover z))
    _ ≤ T.sum (fun t => (ball t).card) := Finset.card_biUnion_le
    _ ≤ T.sum (fun _ => B) := Finset.sum_le_sum (fun t _ => ball_bound t)
    _ = T.card * B := by simp [Finset.sum_const, smul_eq_mul]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[self_mem_sparseBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma self_mem_sparseBall
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (hk : 2 ≤ k) :
-- imply
  x ∈ sparseBall d k x := by
-- proof
  simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
  have : (Finset.univ.filter fun i => x.val i ≠ x.val i) = ∅ := by ext i; simp
  rw [this, Finset.card_empty]; omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparseBall_subset_sparseBallCeil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparseBall_subset_sparseBallCeil
  {d k : ℕ}
  {x : SparseVec d k} :
-- imply
  sparseBall d k x ⊆ sparseBallCeil d k x := by
-- proof
  intro y hy
  simp only [sparseBall, sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[eq_of_supp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma eq_of_supp_eq
  {d : ℕ}
  {f g : Fin d → Bool}
-- given
  (h : supp f = supp g) :
-- imply
  f = g := by
-- proof
  ext i
  have hiff : f i = true ↔ g i = true := by
    constructor <;> intro hi
    · have : i ∈ supp f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [h] at this; exact (Finset.mem_filter.mp this).2
    · have : i ∈ supp g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [← h] at this; exact (Finset.mem_filter.mp this).2
  cases hf : f i <;> cases hg : g i <;> simp_all

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[hammingDist_eq_sdiff_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma hammingDist_eq_sdiff_sum
  {d : ℕ}
  {f g : Fin d → Bool} :
-- imply
  hammingDist f g = (supp f \ supp g).card + (supp g \ supp f).card := by
-- proof
  unfold hammingDist
  rw [← Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  congr 1; ext i
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro h; cases hf : f i <;> cases hg : g i <;> simp_all
  · rintro (⟨hf, hg⟩ | ⟨hg, hf⟩) <;> simp_all

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[card_sdiff_eq_of_card_eq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma card_sdiff_eq_of_card_eq'
  [DecidableEq α]
  {A B : Finset α}
-- given
  (h : A.card = B.card) :
-- imply
  (A \ B).card = (B \ A).card := by
-- proof
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h2; omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sdiff_supp_subset_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sdiff_supp_subset_compl
  {d : ℕ}
  {f g : Fin d → Bool} :
-- imply
  supp f \ supp g ⊆ (supp g)ᶜ := by
-- proof
  rw [Finset.compl_eq_univ_sdiff]
  intro i hi
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi ⊢
  exact hi.2

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparseBallCeil_card_le_tight](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparseBallCeil_card_le_tight
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (_hk : 2 ≤ k)
  (_hkd : k ≤ d / 8) :
-- imply
  (sparseBallCeil d k x).card ≤ ∑ j ∈ Finset.range ((k + 3) / 4), Nat.choose k j * Nat.choose (d - k) j := by
-- proof
  classical
  set S := supp x.val with hS_def
  have hScard : S.card = k := x.property
  have hSccard : Sᶜ.card = d - k := by
    rw [Finset.card_compl, Fintype.card_fin, hScard]
  let f : SparseVec d k → Finset (Fin d) × Finset (Fin d) :=
    fun y => (S \ supp y.val, supp y.val \ S)
  let target := (Finset.range ((k + 3) / 4)).biUnion
    (fun j => (S.powersetCard j) ×ˢ (Sᶜ.powersetCard j))
  have hf_card : ((sparseBallCeil d k x).image f).card = (sparseBallCeil d k x).card := by
    apply Finset.card_image_of_injOn
    intro y₁ _ y₂ _ heq
    simp only [f, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    apply Subtype.ext; apply eq_of_supp_eq; ext i
    constructor <;> intro hi
    · by_cases hx : i ∈ S
      · have : i ∉ S \ supp y₁.val := fun h => (Finset.mem_sdiff.mp h).2 hi
        rw [h1] at this
        exact by_contra fun hn => this (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
      · have : i ∈ supp y₁.val \ S := Finset.mem_sdiff.mpr ⟨hi, hx⟩
        rw [h2] at this; exact (Finset.mem_sdiff.mp this).1
    · by_cases hx : i ∈ S
      · have : i ∉ S \ supp y₂.val := fun h => (Finset.mem_sdiff.mp h).2 hi
        rw [← h1] at this
        exact by_contra fun hn => this (Finset.mem_sdiff.mpr ⟨hx, hn⟩)
      · have : i ∈ supp y₂.val \ S := Finset.mem_sdiff.mpr ⟨hi, hx⟩
        rw [← h2] at this; exact (Finset.mem_sdiff.mp this).1
  have hf_sub : (sparseBallCeil d k x).image f ⊆ target := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨y, hy_ball, rfl⟩ := hp
    simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and] at hy_ball
    set j := (S \ supp y.val).card
    have hj_eq : (supp y.val \ S).card = j :=
      (card_sdiff_eq_of_card_eq' (by rw [hScard]; exact y.property.symm)).symm
    have hdist_eq : hammingDist x.val y.val = j + j := by
      rw [hammingDist_eq_sdiff_sum x.val y.val, ← hS_def]; omega
    have hj_bound : j < (k + 3) / 4 := by omega
    simp only [f, target, Finset.mem_biUnion, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard]
    exact ⟨j, hj_bound, ⟨⟨Finset.sdiff_subset, rfl⟩,
      ⟨sdiff_supp_subset_compl y.val x.val, hj_eq⟩⟩⟩
  calc (sparseBallCeil d k x).card
    = ((sparseBallCeil d k x).image f).card := hf_card.symm
    _ ≤ target.card := Finset.card_le_card hf_sub
    _ ≤ ∑ j ∈ Finset.range ((k + 3) / 4),
      ((S.powersetCard j) ×ˢ (Sᶜ.powersetCard j)).card :=
      Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range ((k + 3) / 4), Nat.choose k j * Nat.choose (d - k) j := by
      congr 1; ext j
      rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
        hScard, hSccard]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[nat_div_cast_gt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma nat_div_cast_gt
  {a b : ℕ}
-- given
  (hb : 0 < b) :
-- imply
  (↑a : ℝ) / ↑b - 1 < ↑(a / b : ℕ) := by
-- proof
  have hb_pos : (0:ℝ) < ↑b := Nat.cast_pos.mpr hb
  have h1 := Nat.lt_div_mul_add hb (a := a)
  have h2 : (↑a : ℝ) < (↑(a / b : ℕ) + 1) * ↑b := by
    calc (↑a : ℝ) < ↑(a / b * b + b) := by exact_mod_cast h1
      _ = ↑(a / b) * ↑b + ↑b := by push_cast; ring
      _ = (↑(a / b) + 1) * ↑b := by ring
  linarith [(div_lt_iff₀ hb_pos).mpr h2]

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[ceil_exp_choose_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma ceil_exp_choose_le
  {d k j : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkd : k ≤ d / 8)
  (hj : j < (k + 3) / 4) :
-- imply
  Nat.choose (d - k) j * ⌈Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))⌉₊ ≤ Nat.choose (d - k) (k - j) := by
-- proof
  have hk1 : 1 ≤ k := by omega
  have h8kd : 8 * k ≤ d := by omega
  have hkd' : k ≤ d - k := by omega
  have h2j : 2 * j ≤ k := by omega
  set m := k - 2 * j with hm_def
  have hm_pos : 0 < m := by omega
  have hkm_pos : 0 < k ^ m := Nat.pos_of_ne_zero (by positivity)
  have h_ratio := ChernoffHelpers.choose_ratio_bound (d - k) k j h2j hkd'
  set N := ⌈Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))⌉₊
  suffices hN : N * k ^ m ≤ (d - k - k + 1) ^ m by
    have h1 : k ^ m * (Nat.choose (d - k) j * N)
      ≤ (d - k - k + 1) ^ m * Nat.choose (d - k) j := by
      calc k ^ m * (Nat.choose (d - k) j * N)
        = N * k ^ m * Nat.choose (d - k) j := by ring
        _ ≤ (d - k - k + 1) ^ m * Nat.choose (d - k) j :=
          Nat.mul_le_mul_right _ hN
    exact Nat.le_of_mul_le_mul_left (le_trans h1 h_ratio) hkm_pos
  set E := Real.exp ((↑k : ℝ) / 8 * Real.log (1 + (↑d : ℝ) / (2 * ↑k)))
  set dkk1 := d - k - k + 1
  have hk_pos_r : (0 : ℝ) < ↑k := Nat.cast_pos.mpr (by omega)
  have hkm_pos_r : (0 : ℝ) < ↑(k ^ m) := Nat.cast_pos.mpr hkm_pos
  have h6k := ChernoffHelpers.base_ratio_ge_six d k hk1 h8kd
  have hdkk1_eq : (dkk1 : ℕ) = d - 2 * k + 1 := by omega
  have hdkk1_ge_6k : 6 * k ≤ dkk1 := by omega
  set ratio : ℝ := ↑dkk1 / ↑k
  have hratio_pos : ratio > 0 := div_pos (by positivity) hk_pos_r
  have hratio_ge6 : ratio ≥ 6 := by
    rw [ge_iff_le, le_div_iff₀ hk_pos_r]; exact_mod_cast hdkk1_ge_6k
  have hratio_ge1 : 1 ≤ ratio := by linarith
  have hE_le_rpow : E ≤ ratio ^ ((↑k : ℝ) / 2) := by
    have h_exp := ChernoffHelpers.exp_le_ratio_pow (↑d : ℝ) (↑k : ℝ)
      (by exact_mod_cast hk1 : (↑k : ℝ) ≥ 1)
      (by exact_mod_cast h8kd : (↑d : ℝ) ≥ 8 * ↑k)
    suffices h : ((↑d : ℝ) - 2 * ↑k + 1) / ↑k = ratio from by rwa [h] at h_exp
    congr 1
    have h2k : 2 * k ≤ d := by omega
    rw [hdkk1_eq, show d - 2 * k + 1 = (d - 2 * k) + 1 from by omega]
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub h2k, Nat.cast_mul]; ring
  have hm_ge : (↑m : ℝ) ≥ (↑k : ℝ) / 2 + 1 / 2 := by
    have h1 : (↑m : ℝ) ≥ ↑(k / 2) + 1 := by exact_mod_cast show m ≥ k / 2 + 1 by omega
    have h2 : k ≤ 2 * (k / 2) + 1 := by omega
    linarith [show (↑k : ℝ) ≤ 2 * ↑(k / 2 : ℕ) + 1 from by exact_mod_cast h2]
  have hE_ge1 : E ≥ 1 := by
    apply Real.one_le_exp
    apply mul_nonneg
    · positivity
    · apply Real.log_nonneg
      linarith [div_nonneg (show (0:ℝ) ≤ ↑d from by positivity)
        (by positivity : (0:ℝ) < 2 * ↑k).le]
  have hratio_m_ge_2E : ratio ^ m ≥ 2 * E := by
    suffices h : ratio ^ m ≥ 2 * ratio ^ ((↑k : ℝ) / 2) by linarith
    rw [show ratio ^ m = ratio ^ (↑m : ℝ) from (Real.rpow_natCast ratio m).symm,
      show (↑m : ℝ) = ↑k / 2 + (↑m - ↑k / 2) from by ring,
      Real.rpow_add hratio_pos]
    have hrkpos : ratio ^ ((↑k : ℝ) / 2) > 0 := Real.rpow_pos_of_pos hratio_pos _
    suffices h : ratio ^ ((↑m : ℝ) - ↑k / 2) ≥ 2 by nlinarith
    calc ratio ^ ((↑m : ℝ) - ↑k / 2)
      ≥ ratio ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hratio_ge1 (by linarith)
      _ ≥ (6 : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (by norm_num) hratio_ge6 (by norm_num)
      _ ≥ 2 := by
        have h1 : (4:ℝ) ^ ((1:ℝ)/2) ≤ (6:ℝ) ^ ((1:ℝ)/2) :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
        have h2 : (4:ℝ) ^ ((1:ℝ)/2) = 2 := by
          rw [show (4:ℝ) = (2:ℝ) ^ (2:ℕ) from by norm_num,
            show ((2:ℝ) ^ (2:ℕ)) ^ ((1:ℝ)/2) = (2:ℝ) ^ ((2:ℕ) * ((1:ℝ)/2)) from by
              rw [← Real.rpow_natCast (2:ℝ) 2,
                ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]]
          norm_num
        linarith
  have hE_plus1 : E + 1 ≤ ratio ^ m := by linarith
  have hndiv_gt : ratio ^ m - 1 < ↑(dkk1 ^ m / k ^ m : ℕ) := by
    have : ratio ^ m = ↑(dkk1 ^ m) / ↑(k ^ m) := by
      simp [ratio, div_pow, Nat.cast_pow]
    rw [this]
    exact nat_div_cast_gt (dkk1 ^ m) (k ^ m) hkm_pos
  have hN_le : N ≤ dkk1 ^ m / k ^ m := by
    rw [Nat.ceil_le]; linarith
  exact (Nat.le_div_iff_mul_le hkm_pos).mp hN_le

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[chernoff_counting_bound_ceil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma chernoff_counting_bound_ceil
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (hk : 2 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  (sparseBallCeil d k x).card * ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊ ≤ Fintype.card (SparseVec d k) := by
-- proof
  rw [sparsevec_card]
  set E := Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * ↑k)))
  set N := ⌈E⌉₊
  have hball := sparseBallCeil_card_le_tight d k hk hkd x
  have hkd' : k ≤ d := by omega
  calc (sparseBallCeil d k x).card * N
    ≤ (∑ j ∈ Finset.range ((k + 3) / 4),
      Nat.choose k j * Nat.choose (d - k) j) * N :=
      Nat.mul_le_mul_right N hball
    _ = ∑ j ∈ Finset.range ((k + 3) / 4),
      Nat.choose k j * Nat.choose (d - k) j * N := Finset.sum_mul ..
    _ ≤ ∑ j ∈ Finset.range ((k + 3) / 4),
      Nat.choose k j * Nat.choose (d - k) (k - j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [mul_assoc]
      exact Nat.mul_le_mul_left _ (ceil_exp_choose_le d k j hk hkd hj)
    _ ≤ Nat.choose d k := by
      have hdk : d = k + (d - k) := by omega
      have hvand : Nat.choose d k =
        ∑ j ∈ Finset.range (k + 1),
          Nat.choose k j * Nat.choose (d - k) (k - j) := by
        conv_lhs => rw [hdk]
        rwa [Nat.add_choose_eq, ← Nat.succ_eq_add_one]
          (fun i j => Nat.choose k i * Nat.choose (d - k) j) k
      rw [hvand]
      apply Finset.sum_le_sum_of_subset
      apply Finset.range_mono
      omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[chernoff_counting_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma chernoff_counting_bound
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (hk : 2 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  (sparseBall d k x).card * ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊ ≤ Fintype.card (SparseVec d k) :=
-- proof
  calc (sparseBall d k x).card * _ ≤ (sparseBallCeil d k x).card * _ :=
    Nat.mul_le_mul_right _ (Finset.card_le_card (sparseBall_subset_sparseBallCeil d k x))
    _ ≤ _ := chernoff_counting_bound_ceil d k hk hkd x

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[chernoff_ball_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma chernoff_ball_bound
  {d k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≥ Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))) ∧ N ≤ Fintype.card (SparseVec d k) ∧ ∀ x : SparseVec d k, (sparseBall d k x).card * N ≤ Fintype.card (SparseVec d k) := by
-- proof
  let N := ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
  have hkd' : k ≤ d := by omega
  let x₀ := mkSparseVec d k hkd'
  have hbound := chernoff_counting_bound d k hk hkd x₀
  have hself := self_mem_sparseBall d k hk x₀
  have hball_pos : 0 < (sparseBall d k x₀).card := Finset.card_pos.mpr ⟨x₀, hself⟩
  have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hN_le : N ≤ Fintype.card (SparseVec d k) :=
    le_trans (Nat.le_mul_of_pos_left N hball_pos) hbound
  exact ⟨N, hN_pos, Nat.le_ceil _, hN_le, fun x => chernoff_counting_bound d k hk hkd x⟩

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparseVecOfFin_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparseVecOfFin_injective
  {d : ℕ} :
-- imply
  Function.Injective (sparseVecOfFin d) := by
-- proof
  intro i j h
  simp only [sparseVecOfFin, Subtype.mk.injEq] at h
  have := congr_fun h i
  simp [unitVec, beq_iff_eq] at this
  exact this.symm

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparse_vec_k1_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparse_vec_k1_count
  {d : ℕ}
-- given
  (hd : 1 ≤ d / 8) :
-- imply
  (d : ℝ) ≥ Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2)) ∧ d ≤ Fintype.card (SparseVec d 1) := by
-- proof
  constructor
  ·
    have hd8 : 8 ≤ d := by omega
    have hd2_pos : (0 : ℝ) < 1 + (d : ℝ) / 2 := by positivity
    calc Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))
      ≤ Real.exp (Real.log (1 + (d : ℝ) / 2)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_of_le_one_left (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
        linarith
      _ = 1 + (d : ℝ) / 2 := Real.exp_log hd2_pos
      _ ≤ (d : ℝ) := by
        have : (d : ℝ) ≥ 8 := by exact_mod_cast hd8
        linarith
  ·
    have h := Fintype.card_le_of_injective (sparseVecOfFin d) (sparseVecOfFin_injective d)
    rwa [Fintype.card_fin] at h

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[probabilistic_method_sparse_vg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma probabilistic_method_sparse_vg
  {d k : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧ (∀ j : Fin M, l0norm (ω j) = k) ∧ ∀ j k' : Fin M, j ≠ k' → hammingDist (ω j) (ω k') ≥ k / 2 := by
-- proof
  classical
  obtain rfl | hk2 := Nat.eq_or_lt_of_le hk
  ·
    obtain ⟨hd_exp, hd_card⟩ := sparse_vec_k1_count d hkd
    have hd_pos : 0 < d := by omega
    let T := (Finset.univ : Finset (SparseVec d 1))
    have hT_card : d ≤ T.card := by simp only [T, Finset.card_univ]; exact hd_card
    refine ⟨T.card, by omega, fun j => (T.equivFin.symm j).val.val, ?_, ?_, ?_⟩
    ·
      simp only [Nat.cast_one]
      calc (1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * 1))
        = Real.log (Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))) := by
          rw [Real.log_exp]; ring_nf
        _ ≤ Real.log (d : ℝ) := Real.log_le_log (Real.exp_pos _) hd_exp
        _ ≤ Real.log (T.card : ℝ) :=
          Real.log_le_log (Nat.cast_pos.mpr hd_pos) (Nat.cast_le.mpr hT_card)
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' _; simp [Nat.div_eq_of_lt (by norm_num : (1 : ℕ) < 2)]
  ·
    have hk2' : 2 ≤ k := hk2
    obtain ⟨N, hN_pos, hN_exp, hN_le, hN_ball⟩ := chernoff_ball_bound d k hk2' hkd
    have hball_bound : ∀ x : SparseVec d k,
      (sparseBall d k x).card ≤ Fintype.card (SparseVec d k) / N :=
      fun x => (Nat.le_div_iff_mul_le hN_pos).mpr (hN_ball x)
    have hball_self : ∀ x : SparseVec d k, x ∈ sparseBall d k x := by
      intro x
      simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
      simp [Finset.filter_false_of_mem]; omega
    have hball_symm : ∀ x y : SparseVec d k,
      y ∈ sparseBall d k x → x ∈ sparseBall d k y := by
      intro x y; simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hammingDist_comm y.val x.val]; exact id
    let B := Fintype.card (SparseVec d k) / N
    obtain ⟨T, hsize, hT_pack⟩ := greedy_packing_bound (sparseBall d k) B
      hball_self hball_symm hball_bound
    have hB_pos : 0 < B := Nat.div_pos hN_le hN_pos
    have hTN : N ≤ T.card := by
      have : B * N ≤ T.card * B := le_trans (Nat.div_mul_le_self _ _) hsize
      rw [mul_comm T.card B] at this
      exact Nat.le_of_mul_le_mul_left this hB_pos
    have hT_pos : 0 < T.card := Nat.lt_of_lt_of_le hN_pos hTN
    refine ⟨T.card, hT_pos, fun j => (T.equivFin.symm j).val.val, ?_, ?_, ?_⟩
    ·
      calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
        = Real.log (Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))) :=
          (Real.log_exp _).symm
        _ ≤ Real.log (T.card : ℝ) :=
          Real.log_le_log (Real.exp_pos _) (le_trans hN_exp (Nat.cast_le.mpr hTN))
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' hne
      have hj_mem := (T.equivFin.symm j).property
      have hk_mem := (T.equivFin.symm k').property
      have hne' : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
        intro h; exact hne (T.equivFin.symm.injective (Subtype.ext h))
      have := hT_pack _ hj_mem _ hk_mem hne'
      simp only [sparseBall, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
      exact this

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparse_varshamov_gilbert](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparse_varshamov_gilbert
  {d k : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧ (∀ j : Fin M, l0norm (ω j) = k) ∧ ∀ j k' : Fin M, j ≠ k' → hammingDist (ω j) (ω k') ≥ k / 2 :=
-- proof
  probabilistic_method_sparse_vg d k hk hkd

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[chernoff_ball_bound_ceil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma chernoff_ball_bound_ceil
  {d k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≥ Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))) ∧ N ≤ Fintype.card (SparseVec d k) ∧ ∀ x : SparseVec d k, (sparseBallCeil d k x).card * N ≤ Fintype.card (SparseVec d k) := by
-- proof
  let N := ⌈Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))⌉₊
  have hkd' : k ≤ d := by omega
  let x₀ := mkSparseVec d k hkd'
  have hbound := chernoff_counting_bound_ceil d k hk hkd x₀
  have hself : x₀ ∈ sparseBallCeil d k x₀ := by
    simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
    have : (Finset.univ.filter fun i => x₀.val i ≠ x₀.val i) = ∅ := by ext i; simp
    rw [this, Finset.card_empty]; omega
  have hball_pos : 0 < (sparseBallCeil d k x₀).card := Finset.card_pos.mpr ⟨x₀, hself⟩
  have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hN_le : N ≤ Fintype.card (SparseVec d k) :=
    le_trans (Nat.le_mul_of_pos_left N hball_pos) hbound
  exact ⟨N, hN_pos, Nat.le_ceil _, hN_le, fun x => chernoff_counting_bound_ceil d k hk hkd x⟩

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[blockSparseVec_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma blockSparseVec_injective
  {d k : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  Function.Injective (blockSparseVec d k hkd) := by
-- proof
  intro a b heq
  have h1 : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
  simp only [blockSparseVec, Subtype.mk.injEq] at heq
  have haid : a.val * k < d := by nlinarith [a.isLt]
  have hval := congr_fun heq ⟨a.val * k, haid⟩
  simp only [decide_eq_decide] at hval
  have ha_bound : a.val * k ≤ a.val * k ∧ a.val * k < a.val * k + k := ⟨le_refl _, by omega⟩
  rw [iff_true_intro ha_bound] at hval
  obtain ⟨hle, hlt⟩ := hval.mp trivial
  exact Fin.ext (by nlinarith)

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[blockSparseVec_dist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma blockSparseVec_dist
  {d k : ℕ}
  {i j : Fin 8}
-- given
  (_hk : 1 ≤ k)
  (hkd : k ≤ d / 8)
  (hij : i ≠ j) :
-- imply
  hammingDist (blockSparseVec d k hkd i).val (blockSparseVec d k hkd j).val ≥ k := by
-- proof
  unfold hammingDist blockSparseVec
  simp only
  have h8k : 8 * k ≤ d := by have := Nat.div_mul_le_self d 8; omega
  have hik : i.val * k + k ≤ d := by nlinarith [i.isLt]
  calc k = (Finset.univ.filter (fun idx : Fin d =>
    i.val * k ≤ idx.val ∧ idx.val < i.val * k + k)).card :=
    (card_filter_interval d (i.val * k) k hik).symm
    _ ≤ (Finset.univ.filter (fun idx : Fin d =>
      decide (i.val * k ≤ idx.val ∧ idx.val < i.val * k + k) ≠
      decide (j.val * k ≤ idx.val ∧ idx.val < j.val * k + k))).card := by
      apply Finset.card_le_card
      intro ⟨idx, hidx⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      obtain ⟨h1, h2⟩ := hmem
      have hj_false : ¬(j.val * k ≤ idx ∧ idx < j.val * k + k) := by
        intro ⟨hj1, hj2⟩
        obtain hi | hi := Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij)
        · linarith [Nat.mul_le_mul_right k hi]
        · linarith [Nat.mul_le_mul_right k hi]
      have hi_true : decide (i.val * k ≤ idx ∧ idx < i.val * k + k) = true :=
        decide_eq_true_eq.mpr (And.intro h1 h2)
      have hj_f : decide (j.val * k ≤ idx ∧ idx < j.val * k + k) = false :=
        decide_eq_false hj_false
      rw [hi_true, hj_f]; decide

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[nat_ceil_half_ge_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma nat_ceil_half_ge_real
  {k : ℕ}
  {n : ℕ}
-- given
  (h : n ≥ (k + 1) / 2) :
-- imply
  (n : ℝ) ≥ (k : ℝ) / 2 := by
-- proof
  have h2 : k ≤ ((k + 1) / 2) * 2 := by omega
  calc (k : ℝ) / 2 ≤ ((k + 1) / 2 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    exact_mod_cast h2
    _ ≤ (n : ℝ) := by exact_mod_cast h

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[hammingDist_pos_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma hammingDist_pos_of_ne
  {d : ℕ}
  {f g : Fin d → Bool}
-- given
  (h : f ≠ g) :
-- imply
  0 < hammingDist f g := by
-- proof
  unfold hammingDist
  rw [Finset.card_pos]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparseBallCeil_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparseBallCeil_symm
  {d k : ℕ}
  {x y : SparseVec d k} :
-- imply
  y ∈ sparseBallCeil d k x → x ∈ sparseBallCeil d k y := by
-- proof
  simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hammingDist_comm y.val x.val]; exact id

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[self_mem_sparseBallCeil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma self_mem_sparseBallCeil
  {d k : ℕ}
  {x : SparseVec d k}
-- given
  (hk : 2 ≤ k) :
-- imply
  x ∈ sparseBallCeil d k x := by
-- proof
  simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, hammingDist]
  have : (Finset.univ.filter fun i => x.val i ≠ x.val i) = ∅ := by ext i; simp
  rw [this, Finset.card_empty]; omega

end SparseVarshamovGilbert

namespace SparseVarshamovGilbert

/--
[sparse_vg_card_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
lemma sparse_vg_card_bound
  {d k : ℕ}
-- given
  (hk : 1 ≤ k)
  (hkd : k ≤ d / 8) :
-- imply
  ∃ (M : ℕ) (_ : 0 < M) (ω : Fin M → (Fin d → Bool)), 8 ≤ M ∧ Real.log M ≥ (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)) ∧ (∀ j : Fin M, l0norm (ω j) = k) ∧ ∀ j k' : Fin M, j ≠ k' → (hammingDist (ω j) (ω k') : ℝ) ≥ (k : ℝ) / 2 := by
-- proof
  classical
  obtain rfl | hk2 := Nat.eq_or_lt_of_le hk
  ·
    have hd8 : 8 ≤ d := by omega
    obtain ⟨hd_exp, hd_card⟩ := sparse_vec_k1_count d hkd
    have hd_pos : 0 < d := by omega
    let T := (Finset.univ : Finset (SparseVec d 1))
    have hT_card : d ≤ T.card := by simp only [T, Finset.card_univ]; exact hd_card
    have hT8 : 8 ≤ T.card := le_trans hd8 hT_card
    refine ⟨T.card, by omega, fun j => (T.equivFin.symm j).val.val, hT8, ?_, ?_, ?_⟩
    ·
      simp only [Nat.cast_one]
      calc (1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * 1))
        = Real.log (Real.exp ((1 : ℝ) / 8 * Real.log (1 + (d : ℝ) / 2))) := by
          rw [Real.log_exp]; ring_nf
        _ ≤ Real.log (d : ℝ) := Real.log_le_log (Real.exp_pos _) hd_exp
        _ ≤ Real.log (T.card : ℝ) :=
          Real.log_le_log (Nat.cast_pos.mpr hd_pos) (Nat.cast_le.mpr hT_card)
    ·
      intro j; exact (T.equivFin.symm j).val.property
    ·
      intro j k' hjk
      have hne : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
        intro h; exact hjk (T.equivFin.symm.injective (Subtype.ext h))
      have hne_val : (T.equivFin.symm j).val.val ≠ (T.equivFin.symm k').val.val := by
        intro h; exact hne (Subtype.ext h)
      have hdist_pos := hammingDist_pos_of_ne hne_val
      simp only [Nat.cast_one]
      have : (1 : ℝ) ≤ (hammingDist (T.equivFin.symm j).val.val (T.equivFin.symm k').val.val : ℝ) :=
        Nat.one_le_cast.mpr hdist_pos
      linarith
  ·
    have hk2' : 2 ≤ k := hk2
    set expVal := Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))
    set N := ⌈expVal⌉₊ with hN_def
    have hN_pos : 0 < N := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
    have hN_ge : (N : ℝ) ≥ expVal := Nat.le_ceil _
    by_cases hN8 : 8 ≤ N
    ·
      obtain ⟨N', hN'_pos, hN'_exp, hN'_le, hN'_ball⟩ := chernoff_ball_bound_ceil d k hk2' hkd
      have hball_bound : ∀ x : SparseVec d k,
        (sparseBallCeil d k x).card ≤ Fintype.card (SparseVec d k) / N' :=
        fun x => (Nat.le_div_iff_mul_le hN'_pos).mpr (hN'_ball x)
      have hball_self : ∀ x : SparseVec d k, x ∈ sparseBallCeil d k x :=
        fun x => self_mem_sparseBallCeil d k hk2' x
      have hball_symm : ∀ x y : SparseVec d k,
        y ∈ sparseBallCeil d k x → x ∈ sparseBallCeil d k y :=
        fun x y => sparseBallCeil_symm d k x y
      let B := Fintype.card (SparseVec d k) / N'
      obtain ⟨T, hsize, hT_pack⟩ := greedy_packing_bound (sparseBallCeil d k) B
        hball_self hball_symm hball_bound
      have hB_pos : 0 < B := Nat.div_pos hN'_le hN'_pos
      have hTN : N' ≤ T.card := by
        have : B * N' ≤ T.card * B := le_trans (Nat.div_mul_le_self _ _) hsize
        rw [mul_comm T.card B] at this
        exact Nat.le_of_mul_le_mul_left this hB_pos
      have hexpVal_gt : expVal > 7 := by
        have hN_cast : (N : ℝ) ≥ 8 := by exact_mod_cast hN8
        have hceil_bound : (⌈expVal⌉₊ : ℝ) < expVal + 1 :=
          Nat.ceil_lt_add_one (le_of_lt (Real.exp_pos _))
        linarith
      have hN'_ge8 : 8 ≤ N' := by
        have hN'_gt7 : (N' : ℝ) > 7 := lt_of_lt_of_le hexpVal_gt hN'_exp
        exact_mod_cast (show (7 : ℝ) < N' from hN'_gt7)
      have hT8 : 8 ≤ T.card := le_trans hN'_ge8 hTN
      have hT_pos : 0 < T.card := by omega
      refine ⟨T.card, hT_pos, fun j => (T.equivFin.symm j).val.val, hT8, ?_, ?_, ?_⟩
      ·
        calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
          = Real.log (Real.exp ((k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k)))) :=
            (Real.log_exp _).symm
          _ ≤ Real.log (T.card : ℝ) :=
            Real.log_le_log (Real.exp_pos _)
              (le_trans hN'_exp (Nat.cast_le.mpr hTN))
      ·
        intro j; exact (T.equivFin.symm j).val.property
      ·
        intro j k' hne
        have hj_mem := (T.equivFin.symm j).property
        have hk_mem := (T.equivFin.symm k').property
        have hne' : (T.equivFin.symm j).val ≠ (T.equivFin.symm k').val := by
          intro h; exact hne (T.equivFin.symm.injective (Subtype.ext h))
        have := hT_pack _ hj_mem _ hk_mem hne'
        simp only [sparseBallCeil, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at this
        exact nat_ceil_half_ge_real k _ this
    ·
      push Not at hN8
      refine ⟨8, by norm_num, fun j => (blockSparseVec d k hkd j).val, le_refl _, ?_, ?_, ?_⟩
      ·
        have hexp_lt : expVal < 8 := by
          calc expVal ≤ N := hN_ge
            _ < 8 := by exact_mod_cast hN8
        calc (k : ℝ) / 8 * Real.log (1 + (d : ℝ) / (2 * k))
          = Real.log expVal := by rw [Real.log_exp]
          _ ≤ Real.log 8 := Real.log_le_log (Real.exp_pos _) (le_of_lt hexp_lt)
          _ = Real.log (8 : ℕ) := by norm_num
      ·
        intro j; exact (blockSparseVec d k hkd j).property
      ·
        intro j k' hjk
        have hdist := blockSparseVec_dist d k hk hkd j k' hjk
        have h1 : (k : ℝ) ≤ (hammingDist (blockSparseVec d k hkd j).val
          (blockSparseVec d k hkd k').val : ℝ) := Nat.cast_le.mpr hdist
        linarith [Nat.cast_nonneg (α := ℝ) k]
end SparseVarshamovGilbert


/--
[card_filter_val_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
private lemma card_filter_val_lt_eq
  {d k : ℕ}
-- given
  (hkd : k ≤ d) :
-- imply
  (Finset.univ.filter (fun i : Fin d => i.val < k)).card = k := by
-- proof
  apply SparseVarshamovGilbert.card_filter_val_lt d k hkd

/--
[l0norm_unitVec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
private lemma l0norm_unitVec_eq
  {d : ℕ}
  {i : Fin d} :
-- imply
  l0norm (unitVec d i) = 1 := by
-- proof
  apply SparseVarshamovGilbert.l0norm_unitVec d i

/--
[card_filter_interval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Lemma_5_14.lean)
-/
@[path]
private lemma card_filter_interval_eq
  {d a k : ℕ}
-- given
  (h : a + k ≤ d) :
-- imply
  (Finset.univ.filter (fun i : Fin d => a ≤ i.val ∧ i.val < a + k)).card = k := by
-- proof
  apply SparseVarshamovGilbert.card_filter_interval d a k h


-- created on 2026-10-23
