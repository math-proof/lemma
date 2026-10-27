import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.RapidExpansion
open Finset Real HarperIsoperimetric RapidExpansion


namespace RapidExpansion

/--
[bitFlip_bitFlip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma bitFlip_bitFlip
  {n : ℕ}
  {x : HammingCube n} :
-- imply
  bitFlip n (bitFlip n x) = x := by
-- proof
  funext i
  simp [bitFlip]

end RapidExpansion

namespace RapidExpansion

/--
[hammingWt_bitFlip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingWt_bitFlip
  {n : ℕ}
  {x : HammingCube n} :
-- imply
  hammingWt (bitFlip n x) = n - hammingWt x := by
-- proof
  simp only [hammingWt, hammingDist, bitFlip]
  convert_to (Finset.univ.filter fun i : Fin n => x i ≠ false)ᶜ.card =
    n - (Finset.univ.filter fun i : Fin n => x i ≠ false).card
  · congr 1
    ext i
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    cases x i <;> simp
  · rw [Finset.card_compl, Fintype.card_fin]

end RapidExpansion

namespace RapidExpansion

/--
[bitFlip_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma bitFlip_injective
  {n : ℕ} :
-- imply
  Function.Injective (bitFlip n) := by
-- proof
  intro x y hxy
  have := congr_arg (bitFlip n) hxy
  rwa [bitFlip_bitFlip, bitFlip_bitFlip] at this

end RapidExpansion

namespace RapidExpansion

/--
[card_openHammingBall_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma card_openHammingBall_le
  {n : ℕ} :
-- imply
  (openHammingBall n (n / 2)).card ≤ 2 ^ (n - 1) := by
-- proof
  by_cases hn : n = 0
  · subst hn; simp [openHammingBall]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  suffices h : (openHammingBall n (n / 2)).card ≤
    (Finset.univ \ openHammingBall n (n / 2)).card by
    have huniv : (Finset.univ : Finset (HammingCube n)).card = 2 ^ n := by
      simp [Fintype.card_pi, Fintype.card_bool]
    have hsdiff := Finset.card_sdiff_of_subset
      (Finset.subset_univ (openHammingBall n (n / 2)))
    rw [huniv] at hsdiff
    have h_pow : 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ n := by
      have hn1 : n = n - 1 + 1 := by omega
      conv_rhs => rw [hn1, pow_succ]
      ring
    omega
  apply Finset.card_le_card_of_injOn (bitFlip n)
  ·
    intro x hx
    have hx' : hammingWt x < n / 2 := by
      simp only [openHammingBall, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      exact hx
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and,
      openHammingBall, Finset.mem_filter, not_lt]
    rw [hammingWt_bitFlip]
    omega
  ·
    intro x _ y _ hxy
    exact bitFlip_injective n hxy

end RapidExpansion

namespace RapidExpansion

/--
[openHammingBall_isHammingBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma openHammingBall_isHammingBall
  {n : ℕ}
-- given
  (hr : 0 < n / 2) :
-- imply
  IsHammingBall (openHammingBall n (n / 2)) := by
-- proof
  refine ⟨fun _ => false, n / 2 - 1, ?_⟩
  ext x
  simp only [openHammingBall, hammingBallFinset, hammingWt, Finset.mem_filter,
    Finset.mem_univ, true_and]
  omega

end RapidExpansion

namespace RapidExpansion

/--
[hammingExpansion_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingExpansion_zero
  {n : ℕ}
  {S : Finset (HammingCube n)} :
-- imply
  hammingExpansion S 0 = S := by
-- proof
  ext x
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hdist⟩
    have : x = a := by
      funext i
      by_contra h
      have : 0 < (Finset.univ.filter fun j => x j ≠ a j).card := by
        apply Finset.card_pos.mpr
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      simp only [hammingDist] at hdist
      omega
    rw [this]; exact ha
  · intro hx
    exact ⟨x, hx, by simp [hammingDist]⟩

end RapidExpansion

namespace RapidExpansion

/--
[hammingExpansion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingExpansion_empty
  {n : ℕ}
  {t : ℕ} :
-- imply
  hammingExpansion (∅ : Finset (HammingCube n)) t = ∅ := by
-- proof
  ext x
  simp [hammingExpansion]

end RapidExpansion

namespace RapidExpansion

/--
[harper_applied](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma harper_applied
  {n : ℕ}
  {t : ℕ}
  {A : Finset (HammingCube n)}
-- given
  (hA : 2 ^ (n - 1) ≤ A.card) :
-- imply
  (hammingExpansion (openHammingBall n (n / 2)) t).card ≤ (hammingExpansion A t).card := by
-- proof
  have hcard_ball : (openHammingBall n (n / 2)).card ≤ A.card :=
    le_trans (card_openHammingBall_le n) hA
  obtain _ | t := t
  ·
    rwa [hammingExpansion_zero, hammingExpansion_zero]
  ·
    have ht : 0 < t + 1 := Nat.succ_pos t
    by_cases hn2 : n / 2 = 0
    ·
      have h_empty : openHammingBall n (n / 2) = ∅ := by
        rw [hn2]
        ext x
        simp [openHammingBall, hammingWt]
      rw [h_empty, hammingExpansion_empty]
      exact Nat.zero_le _
    ·
      have hn2_pos : 0 < n / 2 := Nat.pos_of_ne_zero hn2
      exact harper_isoperimetric_inequality A (openHammingBall n (n / 2))
        (openHammingBall_isHammingBall n hn2_pos) hcard_ball (t + 1) ht

end RapidExpansion

namespace RapidExpansion

/--
[hammingWt_eq_filter_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingWt_eq_filter_card
  {n : ℕ}
  {x : HammingCube n} :
-- imply
  hammingWt x = (Finset.univ.filter (fun i => x i = true)).card := by
-- proof
  unfold hammingWt hammingDist
  congr 1
  ext i
  simp

end RapidExpansion

namespace RapidExpansion

/--
[hammingDist_self_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingDist_self_eq_zero
  {n : ℕ}
  {x : HammingCube n} :
-- imply
  hammingDist x x = 0 := by
-- proof
  unfold hammingDist; simp

end RapidExpansion

namespace RapidExpansion

/--
[hammingWt_le_add_dist](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingWt_le_add_dist
  {n : ℕ}
  {x y : HammingCube n} :
-- imply
  hammingWt x ≤ hammingWt y + hammingDist x y := by
-- proof
  unfold hammingWt
  suffices h : hammingDist x (fun _ => false) ≤ hammingDist x y + hammingDist y (fun _ => false) by
    omega
  unfold hammingDist
  apply le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  intro hxz
  by_cases hxy : x i ≠ y i
  · left; exact hxy
  · right; push Not at hxy; rw [hxy] at hxz; exact hxz

end RapidExpansion

namespace RapidExpansion

/--
[flip_dist_and_wt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma flip_dist_and_wt
  {n : ℕ}
  {x : HammingCube n}
  {T : Finset (Fin n)}
-- given
  (hT : T ⊆ Finset.univ.filter (fun i => x i = true)) :
-- imply
  let y : HammingCube n := fun i => if i ∈ T then false else x i hammingDist x y = T.card ∧ hammingWt y = hammingWt x - T.card := by
-- proof
  constructor
  · unfold hammingDist
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne
      by_contra hni
      simp only [hni, ite_false] at hne
      exact hne rfl
    · intro hi
      have hxi : x i = true := by
        have hmem := hT hi
        rwa [Finset.mem_filter] at hmem
      simp [hi, hxi]
  · rw [hammingWt_eq_filter_card, hammingWt_eq_filter_card]
    suffices h : (Finset.univ.filter (fun i => (if i ∈ T then false else x i) = true)) =
      (Finset.univ.filter (fun i => x i = true)) \ T by
      rw [h, Finset.card_sdiff_of_subset hT]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hi
      exact ⟨h, hi⟩
    · intro ⟨hxi, hni⟩
      simp [hni, hxi]

end RapidExpansion

namespace RapidExpansion

/--
[expansion_openBall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma expansion_openBall
  {n : ℕ}
  {t : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  hammingExpansion (openHammingBall n (n / 2)) t = openHammingBall n (n / 2 + t) := by
-- proof
  ext x
  simp only [hammingExpansion, openHammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hd⟩
    have hwt := hammingWt_le_add_dist x a
    omega
  · intro hx
    by_cases h : hammingWt x < n / 2
    · exact ⟨x, h, by rw [hammingDist_self_eq_zero]; omega⟩
    · push Not at h
      have hn2 : 0 < n / 2 := Nat.div_pos (by omega) (by omega)
      have hk_le_t : hammingWt x - n / 2 + 1 ≤ t := by omega
      have hk_le_S : hammingWt x - n / 2 + 1 ≤
        (Finset.univ.filter (fun i : Fin n => x i = true)).card := by
        rw [← hammingWt_eq_filter_card]; omega
      obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hk_le_S
      refine ⟨fun i => if i ∈ T then false else x i, ?_, ?_⟩
      · have ⟨_, hwt⟩ := flip_dist_and_wt x T hT_sub
        rw [hwt, hT_card]; omega
      · have ⟨hdist, _⟩ := flip_dist_and_wt x T hT_sub
        rw [hdist, hT_card]; omega

end RapidExpansion

namespace RapidExpansion

/--
[hammingDist_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingDist_symm
  {n : ℕ}
  {x y : HammingCube n} :
-- imply
  hammingDist x y = hammingDist y x := by
-- proof
  simp only [hammingDist]
  congr 1
  ext i
  simp [Ne, eq_comm]

end RapidExpansion

namespace RapidExpansion

/--
[hammingDist_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma hammingDist_triangle
  {n : ℕ}
  {x y z : HammingCube n} :
-- imply
  hammingDist x z ≤ hammingDist x y + hammingDist y z := by
-- proof
  unfold hammingDist
  apply le_trans (Finset.card_le_card _) (Finset.card_union_le _ _)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  intro hxz
  by_cases hxy : x i ≠ y i
  · left; exact hxy
  · right
    push Not at hxy
    rwa [hxy] at hxz

end RapidExpansion

namespace RapidExpansion

/--
[expansion_complement_disjoint_of_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma expansion_complement_disjoint_of_A
  {n : ℕ}
  {A : Finset (HammingCube n)}
  {t : ℕ} :
-- imply
  Disjoint (hammingExpansion (Finset.univ \ hammingExpansion A t) t) A := by
-- proof
  rw [Finset.disjoint_left]
  intro x hx_exp hx_A
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and] at hx_exp
  obtain ⟨a', ha'_compl, hdist_xa'⟩ := hx_exp
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_filter] at ha'_compl
  have h_not : ¬(∃ a ∈ A, hammingDist a' a ≤ t) := ha'_compl
  have h_gt : t < hammingDist a' x := by
    by_contra h
    push Not at h
    exact h_not ⟨x, hx_A, h⟩
  rw [hammingDist_symm] at h_gt
  omega

end RapidExpansion

namespace RapidExpansion

/--
[expansion_expansion_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma expansion_expansion_subset
  {n : ℕ}
  {A : Finset (HammingCube n)}
  {s t : ℕ} :
-- imply
  hammingExpansion (hammingExpansion A s) t ⊆ hammingExpansion A (s + t) := by
-- proof
  intro x hx
  simp only [hammingExpansion, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  obtain ⟨a, ha, hya⟩ := hy
  exact ⟨a, ha, le_trans (hammingDist_triangle x y a) (by omega)⟩

end RapidExpansion

namespace RapidExpansion

/--
[card_univ_hammingCube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/RapidExpansion.lean)
-/
@[path]
lemma card_univ_hammingCube
  {n : ℕ} :
-- imply
  (Finset.univ : Finset (HammingCube n)).card = 2 ^ n := by
-- proof
  simp [Fintype.card_pi, Fintype.card_bool]
/-- Bootstrap lemma: if $|A| \ge e^{-2t^{2}/n} \cdot 2^{n}$, then the $t$-expansion of $A$
already has size at least $2^{n-1}$. -/

end RapidExpansion


-- created on 2026-10-23
