module

public import Mathlib
public import Instance.Analysis.Section_11_1.Part2
public import Abbrev.Analysis.Section_11_1

public section
/-!
# Analysis I, Section 11.1: Partitions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Bounded intervals and partitions.
- Length of an interval; the lengths of a partition sum to the length of the interval.

-/


namespace Chapter11

open BoundedInterval

@[simp]
public theorem BoundedInterval.set_Ioo (a b:ℝ) : (Ioo a b : Set ℝ) = .Ioo a b := by rfl

@[simp]
public theorem BoundedInterval.set_Icc (a b:ℝ) : (Icc a b : Set ℝ) = .Icc a b := by rfl

@[simp]
public theorem BoundedInterval.set_Ioc (a b:ℝ) : (Ioc a b : Set ℝ) = .Ioc a b := by rfl

@[simp]
public theorem BoundedInterval.set_Ico (a b:ℝ) : (Ico a b : Set ℝ) = .Ico a b := by rfl

private theorem BoundedInterval.subset_Icc_set (I : BoundedInterval) :
    (I : Set ℝ) ⊆ Set.Icc I.a I.b := by
  cases I with
  | Ioo _ _ =>
    intro x hx
    simp [set_Ioo] at hx ⊢
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  | Icc _ _ =>
    intro x hx
    simp [set_Icc] at hx ⊢
    exact hx
  | Ioc _ _ =>
    intro x hx
    simp [set_Ioc] at hx ⊢
    exact ⟨le_of_lt hx.1, hx.2⟩
  | Ico _ _ =>
    intro x hx
    simp [set_Ico] at hx ⊢
    exact ⟨hx.1, le_of_lt hx.2⟩

private theorem BoundedInterval.Ioo_subset_set (I : BoundedInterval) :
    Set.Ioo I.a I.b ⊆ (I : Set ℝ) := by
  cases I with
  | Ioo _ _ =>
    intro x hx
    simp [set_Ioo] at hx ⊢
    exact hx
  | Icc _ _ =>
    intro x hx
    simp [set_Icc] at hx ⊢
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  | Ioc _ _ =>
    intro x hx
    simp [set_Ioc] at hx ⊢
    exact ⟨hx.1, le_of_lt hx.2⟩
  | Ico _ _ =>
    intro x hx
    simp [set_Ico] at hx ⊢
    exact ⟨le_of_lt hx.1, hx.2⟩

private theorem BoundedInterval.mem_le {I : BoundedInterval} {x : ℝ}
    (hx : x ∈ (I : Set ℝ)) : I.a ≤ x ∧ x ≤ I.b :=
  subset_Icc_set I hx

/-- Corollary 11.1.6 / Exercise 11.1.2 -/
public theorem BoundedInterval.inter (I J : BoundedInterval) :
    ∃ K : BoundedInterval, (I : Set ℝ) ∩ (J : Set ℝ) = (K : Set ℝ) := by
  let a := I.a ⊔ J.a
  let b := I.b ⊓ J.b
  have haI : I.a ≤ a := le_sup_left
  have haJ : J.a ≤ a := le_sup_right
  have hbI : b ≤ I.b := inf_le_left
  have hbJ : b ≤ J.b := inf_le_right
  have Ioo_sub_I : Set.Ioo a b ⊆ (I : Set ℝ) :=
    (Set.Ioo_subset_Ioo haI hbI).trans (Ioo_subset_set I)
  have Ioo_sub_J : Set.Ioo a b ⊆ (J : Set ℝ) :=
    (Set.Ioo_subset_Ioo haJ hbJ).trans (Ioo_subset_set J)
  have inter_sub_Icc : (I : Set ℝ) ∩ (J : Set ℝ) ⊆ Set.Icc a b := by
    intro x hx
    have hxI := mem_le hx.1
    have hxJ := mem_le hx.2
    exact ⟨sup_le hxI.1 hxJ.1, le_inf hxI.2 hxJ.2⟩
  by_cases hlt : a < b
  ·
    by_cases ha : a ∈ (I : Set ℝ) ∩ (J : Set ℝ)
    ·
      by_cases hb : b ∈ (I : Set ℝ) ∩ (J : Set ℝ)
      ·
        refine ⟨Icc a b, ?_⟩
        ext x
        simp [set_Icc, Set.mem_inter_iff, Set.mem_Icc]
        constructor
        · exact fun hx => inter_sub_Icc hx
        · intro hx
          rcases eq_or_lt_of_le hx.1 with hxa | hxa
          · subst hxa; exact ha
          rcases eq_or_lt_of_le hx.2 with hxb | hxb
          · subst hxb; exact hb
          · exact ⟨Ioo_sub_I ⟨hxa, hxb⟩, Ioo_sub_J ⟨hxa, hxb⟩⟩
      ·
        refine ⟨Ico a b, ?_⟩
        ext x
        simp [set_Ico, Set.mem_inter_iff, Set.mem_Ico]
        constructor
        · intro hx
          have hxcc := inter_sub_Icc hx
          have hne : x ≠ b := fun h => hb (h ▸ hx)
          exact ⟨hxcc.1, lt_of_le_of_ne hxcc.2 hne⟩
        · intro hx
          rcases eq_or_lt_of_le hx.1 with hxa | hxa
          · subst hxa; exact ha
          · exact ⟨Ioo_sub_I ⟨hxa, hx.2⟩, Ioo_sub_J ⟨hxa, hx.2⟩⟩
    ·
      by_cases hb : b ∈ (I : Set ℝ) ∩ (J : Set ℝ)
      ·
        refine ⟨Ioc a b, ?_⟩
        ext x
        simp [set_Ioc, Set.mem_inter_iff, Set.mem_Ioc]
        constructor
        · intro hx
          have hxcc := inter_sub_Icc hx
          have hne : x ≠ a := fun h => ha (h ▸ hx)
          exact ⟨lt_of_le_of_ne hxcc.1 (Ne.symm hne), hxcc.2⟩
        · intro hx
          rcases eq_or_lt_of_le hx.2 with hxb | hxb
          · subst hxb; exact hb
          · exact ⟨Ioo_sub_I ⟨hx.1, hxb⟩, Ioo_sub_J ⟨hx.1, hxb⟩⟩
      ·
        refine ⟨Ioo a b, ?_⟩
        ext x
        simp [set_Ioo, Set.mem_inter_iff, Set.mem_Ioo]
        constructor
        · intro hx
          have hxcc := inter_sub_Icc hx
          have hnea : x ≠ a := fun h => ha (h ▸ hx)
          have hneb : x ≠ b := fun h => hb (h ▸ hx)
          exact ⟨lt_of_le_of_ne hxcc.1 (Ne.symm hnea), lt_of_le_of_ne hxcc.2 hneb⟩
        · intro hx
          exact ⟨Ioo_sub_I hx, Ioo_sub_J hx⟩
  ·
    by_cases heq : a = b
    ·
      by_cases ha : a ∈ (I : Set ℝ) ∩ (J : Set ℝ)
      ·
        refine ⟨Icc a a, ?_⟩
        have hcoe : (Icc a a : Set ℝ) = {a} := by
          simp [set_Icc]
        rw [hcoe]
        ext x
        constructor
        · intro hx
          have hxcc := inter_sub_Icc hx
          exact le_antisymm (heq ▸ hxcc.2) hxcc.1
        · intro hx
          simp at hx
          subst hx
          exact ha
      ·
        refine ⟨Ioo (0 : ℝ) 0, ?_⟩
        have hcoe : (Ioo (0 : ℝ) 0 : Set ℝ) = (∅ : Set ℝ) := by
          simp [set_Ioo]
        rw [hcoe]
        ext x
        simp
        intro hxI hxJ
        have hxcc := inter_sub_Icc ⟨hxI, hxJ⟩
        have hxeq : x = a := le_antisymm (heq ▸ hxcc.2) hxcc.1
        exact ha (hxeq ▸ (⟨hxI, hxJ⟩ : x ∈ (I : Set ℝ) ∩ (J : Set ℝ)))
    ·
      refine ⟨Ioo (0 : ℝ) 0, ?_⟩
      have hcoe : (Ioo (0 : ℝ) 0 : Set ℝ) = (∅ : Set ℝ) := by
        simp [set_Ioo]
      rw [hcoe]
      ext x
      simp
      intro hxI hxJ
      have hxcc := inter_sub_Icc ⟨hxI, hxJ⟩
      exact heq (le_antisymm (le_trans hxcc.1 hxcc.2) (not_lt.mp hlt))

end Chapter11
