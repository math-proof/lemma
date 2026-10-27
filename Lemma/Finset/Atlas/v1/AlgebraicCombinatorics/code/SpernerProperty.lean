import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicCombinatorics.code.SpernerProperty.Part2
open Finset SpernerProperty


namespace SpernerProperty

/--
[raise_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma raise_split
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {φ : ℕ → α → α}
  {start : ℕ}
  {k m : ℕ}
  {x : α} :
-- imply
  raise φ start (k + m) x = raise φ (start + k) m (raise φ start k x) := by
-- proof
  induction m with
  | zero => simp [raise]
  | succ m ih =>
    show φ (start + (k + m)) (raise φ start (k + m) x) =
      φ ((start + k) + m) (raise φ (start + k) m (raise φ start k x))
    rw [ih, Nat.add_assoc]

end SpernerProperty

namespace SpernerProperty

/--
[lower_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma lower_split
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {ψ : ℕ → α → α}
  {start k m : ℕ}
  {x : α}
-- given
  (hkm : k + m ≤ start) :
-- imply
  lower ψ start (k + m) x = lower ψ (start - k) m (lower ψ start k x) := by
-- proof
  induction m with
  | zero => simp [lower]
  | succ m ih =>
    show ψ (start - (k + m)) (lower ψ start (k + m) x) =
      ψ ((start - k) - m) (lower ψ (start - k) m (lower ψ start k x))
    rw [ih (by omega)]; congr 1; omega

end SpernerProperty

namespace SpernerProperty

/--
[raise_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma raise_comparable
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {φ : ℕ → α → α}
  {j : ℕ}
  {x y : α}
-- given
  (hφ_grade : ∀ i, i < j → ∀ x, grade ℕ x = i → grade ℕ (φ i x) = i + 1)
  (hφ_lt : ∀ i, i < j → ∀ x, grade ℕ x = i → x < φ i x)
  (hφ_inj : ∀ i, i < j → ∀ x y, grade ℕ x = i → grade ℕ y = i → φ i x = φ i y → x = y)
  (hx : grade ℕ x ≤ j)
  (hy : grade ℕ y ≤ j)
  (hxy : grade ℕ x ≤ grade ℕ y)
  (heq : raise φ (grade ℕ x) (j - grade ℕ x) x = raise φ (grade ℕ y) (j - grade ℕ y) y) :
-- imply
  x ≤ y := by
-- proof
  have rg : ∀ s k, s ≤ j → k ≤ j - s → ∀ z, grade ℕ z = s →
    grade ℕ (raise φ s k z) = s + k := by
    intro s k hs hk z hz
    induction k with
    | zero => simp [raise, hz]
    | succ k ih =>
      simp only [raise]
      exact (hφ_grade (s + k) (by omega) _ (ih (by omega))).trans (by omega)
  have rl : ∀ s k, s ≤ j → k ≤ j - s → ∀ z, grade ℕ z = s →
    z ≤ raise φ s k z := by
    intro s k hs hk z hz
    induction k with
    | zero => simp [raise]
    | succ k ih =>
      exact le_trans (ih (by omega)) (le_of_lt (hφ_lt (s + k) (by omega) _ (rg s k hs (by omega) z hz)))
  have ri : ∀ s k, s ≤ j → k ≤ j - s → ∀ z w, grade ℕ z = s → grade ℕ w = s →
    raise φ s k z = raise φ s k w → z = w := by
    intro s k hs hk z w hz hw h
    induction k with
    | zero => simp [raise] at h; exact h
    | succ k ih =>
      simp only [raise] at h
      exact ih (by omega) (hφ_inj (s + k) (by omega) _ _
        (rg s k hs (by omega) z hz) (rg s k hs (by omega) w hw) h)
  have hsplit : j - grade ℕ x = (grade ℕ y - grade ℕ x) + (j - grade ℕ y) := by omega
  rw [hsplit, raise_split] at heq
  have hg : grade ℕ x + (grade ℕ y - grade ℕ x) = grade ℕ y := by omega
  rw [hg] at heq
  have hinj := ri (grade ℕ y) (j - grade ℕ y) hy le_rfl
    (raise φ (grade ℕ x) (grade ℕ y - grade ℕ x) x) y
    (by rw [rg (grade ℕ x) _ hx (by omega) x rfl]; omega) rfl heq
  rw [← hinj]
  exact rl (grade ℕ x) (grade ℕ y - grade ℕ x) hx (by omega) x rfl

end SpernerProperty

namespace SpernerProperty

/--
[lower_comparable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma lower_comparable
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {ψ : ℕ → α → α}
  {j n : ℕ}
  {x y : α}
-- given
  (hψ_grade : ∀ i, j < i → i ≤ n → ∀ x, grade ℕ x = i → grade ℕ (ψ i x) = i - 1)
  (hψ_lt : ∀ i, j < i → i ≤ n → ∀ x, grade ℕ x = i → ψ i x < x)
  (hψ_inj : ∀ i, j < i → i ≤ n → ∀ x y, grade ℕ x = i → grade ℕ y = i → ψ i x = ψ i y → x = y)
  (hx : j ≤ grade ℕ x)
  (hy : j ≤ grade ℕ y)
  (hxn : grade ℕ x ≤ n)
  (hyn : grade ℕ y ≤ n)
  (hxy : grade ℕ y ≤ grade ℕ x)
  (heq : lower ψ (grade ℕ x) (grade ℕ x - j) x = lower ψ (grade ℕ y) (grade ℕ y - j) y) :
-- imply
  y ≤ x := by
-- proof
  have lg : ∀ s k, j ≤ s → s ≤ n → k ≤ s - j → ∀ z, grade ℕ z = s →
    grade ℕ (lower ψ s k z) = s - k := by
    intro s k hs hsn hk z hz
    induction k with
    | zero => simp [lower, hz]
    | succ k ih =>
      simp only [lower]
      exact (hψ_grade (s - k) (by omega) (by omega) _ (ih (by omega))).trans (by omega)
  have ll : ∀ s k, j ≤ s → s ≤ n → k ≤ s - j → ∀ z, grade ℕ z = s →
    lower ψ s k z ≤ z := by
    intro s k hs hsn hk z hz
    induction k with
    | zero => simp [lower]
    | succ k ih =>
      exact le_of_lt (lt_of_lt_of_le
        (hψ_lt (s - k) (by omega) (by omega) _ (lg s k hs hsn (by omega) z hz)) (ih (by omega)))
  have li : ∀ s k, j ≤ s → s ≤ n → k ≤ s - j → ∀ z w, grade ℕ z = s → grade ℕ w = s →
    lower ψ s k z = lower ψ s k w → z = w := by
    intro s k hs hsn hk z w hz hw h
    induction k with
    | zero => simp [lower] at h; exact h
    | succ k ih =>
      simp only [lower] at h
      exact ih (by omega) (hψ_inj (s - k) (by omega) (by omega) _ _
        (lg s k hs hsn (by omega) z hz) (lg s k hs hsn (by omega) w hw) h)
  have hsplit : grade ℕ x - j = (grade ℕ x - grade ℕ y) + (grade ℕ y - j) := by omega
  rw [hsplit, lower_split ψ (grade ℕ x) _ _ x (by omega)] at heq
  have hg : grade ℕ x - (grade ℕ x - grade ℕ y) = grade ℕ y := by omega
  rw [hg] at heq
  have hinj := li (grade ℕ y) (grade ℕ y - j) hy hyn le_rfl
    (lower ψ (grade ℕ x) (grade ℕ x - grade ℕ y) x) y
    (by rw [lg (grade ℕ x) _ hx hxn (by omega) x rfl]; omega) rfl heq
  rw [← hinj]
  exact ll (grade ℕ x) (grade ℕ x - grade ℕ y) hx hxn (by omega) x rfl

end SpernerProperty

namespace SpernerProperty

/--
[raise_le_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma raise_le_bounded
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {φ : ℕ → α → α}
  {start : ℕ}
  {bound : ℕ}
  {x : α}
  {k : ℕ}
-- given
  (hφ_grade : ∀ i, i < bound → ∀ x, grade ℕ x = i → grade ℕ (φ i x) = i + 1)
  (hφ_lt : ∀ i, i < bound → ∀ x, grade ℕ x = i → x < φ i x)
  (hx : grade ℕ x = start)
  (hk : start + k ≤ bound) :
-- imply
  x ≤ raise φ start k x := by
-- proof
  suffices ∀ m, m ≤ k → grade ℕ (raise φ start m x) = start + m ∧ x ≤ raise φ start m x by
    exact (this k le_rfl).2
  intro m hm
  induction m with
  | zero => simp [raise, hx]
  | succ m ih =>
    obtain ⟨ihm_grade, ihm_le⟩ := ih (by omega)
    constructor
    · simp only [raise]
      exact (hφ_grade (start + m) (by omega) _ ihm_grade).trans (by omega)
    · exact le_trans ihm_le (le_of_lt (hφ_lt (start + m) (by omega) _ ihm_grade))

end SpernerProperty

namespace SpernerProperty

/--
[lower_le_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma lower_le_bounded
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {ψ : ℕ → α → α}
  {start : ℕ}
  {j_bound n_bound : ℕ}
  {x : α}
  {k : ℕ}
-- given
  (hψ_grade : ∀ i, j_bound < i → i ≤ n_bound → ∀ x, grade ℕ x = i → grade ℕ (ψ i x) = i - 1)
  (hψ_lt : ∀ i, j_bound < i → i ≤ n_bound → ∀ x, grade ℕ x = i → ψ i x < x)
  (hx : grade ℕ x = start)
  (hk : k ≤ start - j_bound)
  (hn : start ≤ n_bound) :
-- imply
  lower ψ start k x ≤ x := by
-- proof
  suffices ∀ m, m ≤ k → grade ℕ (lower ψ start m x) = start - m ∧ lower ψ start m x ≤ x by
    exact (this k le_rfl).2
  intro m hm
  induction m with
  | zero => simp [lower, hx]
  | succ m ih =>
    obtain ⟨ihm_grade, ihm_le⟩ := ih (by omega)
    constructor
    · simp only [lower]
      exact (hψ_grade (start - m) (by omega) (by omega) _ ihm_grade).trans (by omega)
    · exact le_of_lt (lt_of_lt_of_le (hψ_lt (start - m) (by omega) (by omega) _ ihm_grade) ihm_le)

end SpernerProperty

namespace SpernerProperty

/--
[rankCount_le_succ_of_raising](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma rankCount_le_succ_of_raising
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {i : ℕ}
-- given
  (hmatch : HasOrderRaisingMatching (α := α) i) :
-- imply
  rankCount (α := α) i ≤ rankCount (α := α) (i + 1) := by
-- proof
  obtain ⟨φ, hgrade, _, hinj⟩ := hmatch
  unfold rankCount
  apply Finset.card_le_card_of_injOn φ
  · intro x hx; rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hgrade x hx.2⟩
  · intro x hx y hy hxy; rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact hinj x y hx.2 hy.2 hxy

end SpernerProperty

namespace SpernerProperty

/--
[rankCount_le_pred_of_lowering](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma rankCount_le_pred_of_lowering
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  {i : ℕ}
-- given
  (hmatch : HasOrderLoweringMatching (α := α) i) :
-- imply
  rankCount (α := α) i ≤ rankCount (α := α) (i - 1) := by
-- proof
  obtain ⟨ψ, hgrade, _, hinj⟩ := hmatch
  unfold rankCount
  apply Finset.card_le_card_of_injOn ψ
  · intro x hx; rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hgrade x hx.2⟩
  · intro x hx y hy hxy; rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    exact hinj x y hx.2 hy.2 hxy

end SpernerProperty

namespace SpernerProperty

/--
[rankCount_le_maxRankCount](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma rankCount_le_maxRankCount
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [GradedPoset α]
  {j : ℕ}
-- given
  (hj : j ≤ GradedPoset.rank (α := α)) :
-- imply
  rankCount (α := α) j ≤ maxRankCount (α := α) := by
-- proof
  unfold maxRankCount
  apply Finset.le_sup (f := fun i => rankCount (α := α) i)
  simp [Finset.mem_range]; omega

end SpernerProperty

namespace SpernerProperty

/--
[orderMatchings_imp_unimodal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma orderMatchings_imp_unimodal
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [GradedPoset α]
  {j : ℕ}
-- given
  (hmatch : HasOrderMatchings (α := α) j) :
-- imply
  IsRankUnimodal (α := α) := by
-- proof
  obtain ⟨hj, hraise, hlower⟩ := hmatch
  refine ⟨j, hj, ?_, ?_⟩
  · intro i₁ i₂ h12 h2j
    induction h12 with
    | refl => exact le_refl _
    | @step m hle ih =>
      have hle' : i₁ ≤ m := hle
      exact le_trans (ih (by omega)) (rankCount_le_succ_of_raising m (hraise m (by omega)))
  · intro i₁ i₂ hj1 h12 h2n
    induction h12 with
    | refl => exact le_refl _
    | @step m hle ih =>
      have hle' : i₁ ≤ m := hle
      have hlow := rankCount_le_pred_of_lowering (m + 1)
        (hlower (m + 1) (by omega) h2n)
      simp only [Nat.add_sub_cancel] at hlow
      exact le_trans hlow (ih (by omega))

end SpernerProperty

namespace SpernerProperty

/--
[orderMatchings_imp_sperner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma orderMatchings_imp_sperner
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [GradedPoset α]
  {j : ℕ}
-- given
  (hmatch : HasOrderMatchings (α := α) j) :
-- imply
  HasSpernerProperty (α := α) := by
-- proof
  classical
  obtain ⟨hj, hraise, hlower⟩ := hmatch
  let φ : ℕ → α → α := fun i x =>
    if h : i < j then (hraise i h).choose x else x
  let ψ : ℕ → α → α := fun i x =>
    if h : j < i ∧ i ≤ GradedPoset.rank (α := α) then (hlower i h.1 h.2).choose x else x
  have φ_grade : ∀ i, i < j → ∀ x, grade ℕ x = i → grade ℕ (φ i x) = i + 1 := by
    intro i hi x hx; simp only [φ, dif_pos hi]; exact (hraise i hi).choose_spec.1 x hx
  have φ_lt : ∀ i, i < j → ∀ x, grade ℕ x = i → x < φ i x := by
    intro i hi x hx; simp only [φ, dif_pos hi]; exact (hraise i hi).choose_spec.2.1 x hx
  have φ_inj : ∀ i, i < j → ∀ x y, grade ℕ x = i → grade ℕ y = i → φ i x = φ i y → x = y := by
    intro i hi x y hx hy hxy; simp only [φ, dif_pos hi] at hxy
    exact (hraise i hi).choose_spec.2.2 x y hx hy hxy
  have ψ_grade : ∀ i, j < i → i ≤ GradedPoset.rank (α := α) →
    ∀ x, grade ℕ x = i → grade ℕ (ψ i x) = i - 1 := by
    intro i hi1 hi2 x hx; simp only [ψ, dif_pos (And.intro hi1 hi2)]
    exact (hlower i hi1 hi2).choose_spec.1 x hx
  have ψ_lt : ∀ i, j < i → i ≤ GradedPoset.rank (α := α) →
    ∀ x, grade ℕ x = i → ψ i x < x := by
    intro i hi1 hi2 x hx; simp only [ψ, dif_pos (And.intro hi1 hi2)]
    exact (hlower i hi1 hi2).choose_spec.2.1 x hx
  have ψ_inj : ∀ i, j < i → i ≤ GradedPoset.rank (α := α) →
    ∀ x y, grade ℕ x = i → grade ℕ y = i → ψ i x = ψ i y → x = y := by
    intro i hi1 hi2 x y hx hy hxy; simp only [ψ, dif_pos (And.intro hi1 hi2)] at hxy
    exact (hlower i hi1 hi2).choose_spec.2.2 x y hx hy hxy
  let n := GradedPoset.rank (α := α)
  let toJ : α → α := fun x =>
    if grade ℕ x ≤ j then
      raise φ (grade ℕ x) (j - grade ℕ x) x
    else
      lower ψ (grade ℕ x) (grade ℕ x - j) x
  intro A hA
  suffices A.card ≤ rankCount (α := α) j by
    exact le_trans this (rankCount_le_maxRankCount j hj)
  unfold rankCount
  apply Finset.card_le_card_of_injOn toJ
  ·
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [toJ]
    split_ifs with h
    ·
      have : ∀ k, k ≤ j - grade ℕ x →
        grade ℕ (raise φ (grade ℕ x) k x) = grade ℕ x + k := by
        intro k hk
        induction k with
        | zero => simp [raise]
        | succ k ih =>
          simp only [raise]
          exact (φ_grade (grade ℕ x + k) (by omega) _ (ih (by omega))).trans (by omega)
      exact (this (j - grade ℕ x) le_rfl).trans (by omega)
    ·
      push_neg at h
      have hgx : grade ℕ x ≤ n := GradedPoset.grade_le_rank x
      have : ∀ k, k ≤ grade ℕ x - j →
        grade ℕ (lower ψ (grade ℕ x) k x) = grade ℕ x - k := by
        intro k hk
        induction k with
        | zero => simp [lower]
        | succ k ih =>
          simp only [lower]
          exact (ψ_grade (grade ℕ x - k) (by omega) (by omega) _ (ih (by omega))).trans (by omega)
      exact (this (grade ℕ x - j) le_rfl).trans (by omega)
  ·
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    simp only [toJ] at hxy
    by_cases hxj : grade ℕ x ≤ j <;> by_cases hyj : grade ℕ y ≤ j
    ·
      rw [if_pos hxj, if_pos hyj] at hxy
      by_cases hle : grade ℕ x ≤ grade ℕ y
      · have hxy_le := raise_comparable φ j φ_grade φ_lt φ_inj x y hxj hyj hle hxy
        by_contra hne; exact hA hx hy hne hxy_le
      · push_neg at hle
        have hyx_le := raise_comparable φ j φ_grade φ_lt φ_inj y x hyj hxj (le_of_lt hle) hxy.symm
        by_contra hne; exact hA hy hx (Ne.symm hne) hyx_le
    ·
      rw [if_pos hxj, if_neg hyj] at hxy
      push_neg at hyj
      have hgy : grade ℕ y ≤ n := GradedPoset.grade_le_rank y
      have hx_le : x ≤ raise φ (grade ℕ x) (j - grade ℕ x) x :=
        raise_le_bounded φ (grade ℕ x) j φ_grade φ_lt x rfl (j - grade ℕ x) (by omega)
      have hy_le : lower ψ (grade ℕ y) (grade ℕ y - j) y ≤ y :=
        lower_le_bounded ψ (grade ℕ y) j n ψ_grade ψ_lt y rfl (grade ℕ y - j) (by omega) hgy
      have : x ≤ y := le_trans hx_le (hxy ▸ hy_le)
      by_contra hne; exact hA hx hy hne this
    ·
      rw [if_neg hxj, if_pos hyj] at hxy
      push_neg at hxj
      have hgx : grade ℕ x ≤ n := GradedPoset.grade_le_rank x
      have hy_le : y ≤ raise φ (grade ℕ y) (j - grade ℕ y) y :=
        raise_le_bounded φ (grade ℕ y) j φ_grade φ_lt y rfl (j - grade ℕ y) (by omega)
      have hx_le : lower ψ (grade ℕ x) (grade ℕ x - j) x ≤ x :=
        lower_le_bounded ψ (grade ℕ x) j n ψ_grade ψ_lt x rfl (grade ℕ x - j) (by omega) hgx
      have : y ≤ x := le_trans hy_le (hxy.symm ▸ hx_le)
      by_contra hne; exact hA hy hx (Ne.symm hne) this
    ·
      rw [if_neg hxj, if_neg hyj] at hxy
      push_neg at hxj hyj
      have hgx : grade ℕ x ≤ n := GradedPoset.grade_le_rank x
      have hgy : grade ℕ y ≤ n := GradedPoset.grade_le_rank y
      by_cases hle : grade ℕ y ≤ grade ℕ x
      · have hyx_le := lower_comparable ψ j n ψ_grade ψ_lt ψ_inj
        x y (by omega) (by omega) hgx hgy hle hxy
        by_contra hne; exact hA hy hx (Ne.symm hne) hyx_le
      · push_neg at hle
        have hxy_le := lower_comparable ψ j n ψ_grade ψ_lt ψ_inj
          y x (by omega) (by omega) hgy hgx (le_of_lt hle) hxy.symm
        by_contra hne; exact hA hx hy hne hxy_le

end SpernerProperty

namespace SpernerProperty

/--
[hasSpernerProperty_of_orderIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma hasSpernerProperty_of_orderIso
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [PartialOrder P]
  [Fintype P]
  [DecidableEq P]
  [GradeMinOrder ℕ P]
  [GradedPoset P]
  [PartialOrder Q]
  [Fintype Q]
  [DecidableEq Q]
  [GradeMinOrder ℕ Q]
  [GradedPoset Q]
  {e : P ≃o Q}
-- given
  (hgrade : ∀ p : P, grade ℕ (e p) = grade ℕ p)
  (hP : HasSpernerProperty (α := P)) :
-- imply
  HasSpernerProperty (α := Q) := by
-- proof
  have hgrade_symm : ∀ q : Q, grade ℕ (e.symm q) = grade ℕ q := by
    intro q
    have := hgrade (e.symm q)
    simp only [OrderIso.apply_symm_apply] at this
    exact this.symm
  have hrank : GradedPoset.rank (α := P) = GradedPoset.rank (α := Q) := by
    apply le_antisymm
    · obtain ⟨p, hp⟩ := GradedPoset.grade_rank_exists (α := P)
      have := GradedPoset.grade_le_rank (α := Q) (e p)
      rw [hgrade] at this
      omega
    · obtain ⟨q, hq⟩ := GradedPoset.grade_rank_exists (α := Q)
      have := GradedPoset.grade_le_rank (α := P) (e.symm q)
      rw [hgrade_symm] at this
      omega
  have hrankCount : ∀ i, rankCount (α := Q) i = rankCount (α := P) i := by
    intro i
    unfold rankCount
    apply le_antisymm
    ·
      apply Finset.card_le_card_of_injOn e.symm
      · intro q hq
        rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
        exact ⟨Finset.mem_univ _, by rw [hgrade_symm]; exact hq.2⟩
      · intro q₁ _ q₂ _ h
        exact e.symm.injective h
    ·
      apply Finset.card_le_card_of_injOn e
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
        exact ⟨Finset.mem_univ _, by rw [hgrade]; exact hp.2⟩
      · intro p₁ _ p₂ _ h
        exact e.injective h
  have hmaxRankCount : maxRankCount (α := Q) = maxRankCount (α := P) := by
    unfold maxRankCount
    rw [hrank]
    exact Finset.sup_congr rfl (fun i _ => hrankCount i)
  intro A hA
  let B := A.image e.symm
  have hB_antichain : IsAntichain (· ≤ ·) (B : Set P) := by
    intro x hx y hy hne hle
    rw [Finset.mem_coe, Finset.mem_image] at hx hy
    obtain ⟨qx, hqx, rfl⟩ := hx
    obtain ⟨qy, hqy, rfl⟩ := hy
    have hne' : qx ≠ qy := fun heq => hne (by rw [heq])
    exact hA (Finset.mem_coe.mpr hqx) (Finset.mem_coe.mpr hqy) hne' (e.symm.le_iff_le.mp hle)
  have hB_card : B.card = A.card :=
    Finset.card_image_of_injective A e.symm.injective
  have hB_bound := hP B hB_antichain
  rw [hmaxRankCount]
  rwa [hB_card] at hB_bound

end SpernerProperty

namespace SpernerProperty

/--
[isRankUnimodal_of_orderIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SpernerProperty.lean)
-/
@[path]
lemma isRankUnimodal_of_orderIso
  [PartialOrder α]
  [Fintype α]
  [DecidableEq α]
  [GradeMinOrder ℕ α]
  [PartialOrder P]
  [Fintype P]
  [DecidableEq P]
  [GradeMinOrder ℕ P]
  [GradedPoset P]
  [PartialOrder Q]
  [Fintype Q]
  [DecidableEq Q]
  [GradeMinOrder ℕ Q]
  [GradedPoset Q]
  {e : P ≃o Q}
-- given
  (hgrade : ∀ p : P, grade ℕ (e p) = grade ℕ p)
  (hP : IsRankUnimodal (α := P)) :
-- imply
  IsRankUnimodal (α := Q) := by
-- proof
  have hgrade_symm : ∀ q : Q, grade ℕ (e.symm q) = grade ℕ q := by
    intro q
    have := hgrade (e.symm q)
    simp only [OrderIso.apply_symm_apply] at this
    exact this.symm
  have hrank : GradedPoset.rank (α := P) = GradedPoset.rank (α := Q) := by
    apply le_antisymm
    · obtain ⟨p, hp⟩ := GradedPoset.grade_rank_exists (α := P)
      have := GradedPoset.grade_le_rank (α := Q) (e p)
      rw [hgrade] at this
      omega
    · obtain ⟨q, hq⟩ := GradedPoset.grade_rank_exists (α := Q)
      have := GradedPoset.grade_le_rank (α := P) (e.symm q)
      rw [hgrade_symm] at this
      omega
  have hrankCount : ∀ i, rankCount (α := Q) i = rankCount (α := P) i := by
    intro i
    unfold rankCount
    apply le_antisymm
    · apply Finset.card_le_card_of_injOn e.symm
      · intro q hq
        rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
        exact ⟨Finset.mem_univ _, by rw [hgrade_symm]; exact hq.2⟩
      · intro q₁ _ q₂ _ h
        exact e.symm.injective h
    · apply Finset.card_le_card_of_injOn e
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_filter] at hp ⊢
        exact ⟨Finset.mem_univ _, by rw [hgrade]; exact hp.2⟩
      · intro p₁ _ p₂ _ h
        exact e.injective h
  obtain ⟨j, hj_le, hincr, hdecr⟩ := hP
  refine ⟨j, ?_, ?_, ?_⟩
  · omega
  · intro i₁ i₂ h₁₂ h₂j
    have h1 := hincr i₁ i₂ h₁₂ h₂j
    rwa [← hrankCount, ← hrankCount] at h1
  · intro i₁ i₂ hj₁ h₁₂ h₂n
    have h1 := hdecr i₁ i₂ hj₁ h₁₂ (by omega)
    rwa [← hrankCount, ← hrankCount] at h1

end SpernerProperty


-- created on 2026-10-23
