module

public import Mathlib
public import Abbrev.Analysis.Section_11_1.Part3

public section

namespace Chapter11

open BoundedInterval

public theorem BoundedInterval.join_Icc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) :
    (Icc a c).joins (Icc a b) (Ioc b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x ≤ b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨lt_of_not_ge hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, le_trans h.2 hbc⟩
      | inr h => exact ⟨le_trans hab (le_of_lt h.1), h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans hab hbc))]

public theorem BoundedInterval.join_Icc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) :
    (Ico a c).joins (Icc a b) (Ioo b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x ≤ b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨lt_of_not_ge hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, lt_of_le_of_lt h.2 hbc⟩
      | inr h => exact ⟨le_trans hab (le_of_lt h.1), h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr (le_of_lt hbc)),
      max_eq_left (sub_nonneg.mpr (le_trans hab (le_of_lt hbc)))]

public theorem BoundedInterval.join_Ioc_Ioc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) :
    (Ioc a c).joins (Ioc a b) (Ioc b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x ≤ b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨lt_of_not_ge hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, le_trans h.2 hbc⟩
      | inr h => exact ⟨lt_of_le_of_lt hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans hab hbc))]

public theorem BoundedInterval.join_Ioc_Ioo {a b c:ℝ} (hab: a ≤ b) (hbc: b < c) :
    (Ioo a c).joins (Ioc a b) (Ioo b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x ≤ b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨lt_of_not_ge hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, lt_of_le_of_lt h.2 hbc⟩
      | inr h => exact ⟨lt_of_le_of_lt hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr (le_of_lt hbc)),
      max_eq_left (sub_nonneg.mpr (le_trans hab (le_of_lt hbc)))]

public theorem BoundedInterval.join_Ico_Icc {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) :
    (Icc a c).joins (Ico a b) (Icc b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x < b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨le_of_not_gt hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, le_trans (le_of_lt h.2) hbc⟩
      | inr h => exact ⟨le_trans hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans hab hbc))]

public theorem BoundedInterval.join_Ico_Ico {a b c:ℝ} (hab: a ≤ b) (hbc: b ≤ c) :
    (Ico a c).joins (Ico a b) (Ico b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x < b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨le_of_not_gt hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, lt_of_lt_of_le h.2 hbc⟩
      | inr h => exact ⟨le_trans hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr hab), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans hab hbc))]

public theorem BoundedInterval.join_Ioo_Icc {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) :
    (Ioc a c).joins (Ioo a b) (Icc b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x < b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨le_of_not_gt hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, le_trans (le_of_lt h.2) hbc⟩
      | inr h => exact ⟨lt_of_lt_of_le hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr (le_of_lt hab)), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans (le_of_lt hab) hbc))]

public theorem BoundedInterval.join_Ioo_Ico {a b c:ℝ} (hab: a < b) (hbc: b ≤ c) :
    (Ioo a c).joins (Ioo a b) (Ico b c) := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      linarith
    · intro hx
      exact False.elim hx
  · ext x
    constructor
    · intro hx
      simp [BoundedInterval.toSet] at hx
      have hax := hx.1
      have hxc := hx.2
      by_cases hxb : x < b
      · left; exact ⟨hax, hxb⟩
      · right; exact ⟨le_of_not_gt hxb, hxc⟩
    · intro hx
      simp [BoundedInterval.toSet] at hx ⊢
      cases hx with
      | inl h => exact ⟨h.1, lt_of_lt_of_le h.2 hbc⟩
      | inr h => exact ⟨lt_of_lt_of_le hab h.1, h.2⟩
  · simp [BoundedInterval.length, BoundedInterval.a, BoundedInterval.b,
      max_eq_left (sub_nonneg.mpr (le_of_lt hab)), max_eq_left (sub_nonneg.mpr hbc),
      max_eq_left (sub_nonneg.mpr (le_trans (le_of_lt hab) hbc))]

end Chapter11
