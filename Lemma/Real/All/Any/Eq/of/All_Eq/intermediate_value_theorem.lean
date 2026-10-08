import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Topology.Order.IntermediateValue


@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b y : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ∀ xi ∈ Set.Icc a b, ContinuousAt f xi)
  (hy : y ∈ Set.Icc (Minima (Set.Icc a b) f) (Maxima (Set.Icc a b) f)) :
-- imply
  ∃ x ∈ Set.Icc a b, f x = y := by
-- proof
  have hfc : ContinuousOn f (Set.Icc a b) := fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨x₁, hx₁, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hfc
  obtain ⟨x₂, hx₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hfc
  have h₁ : Minima (Set.Icc a b) f = f x₁ := by
    simp only [Minima]
    apply IsLeast.csInf_eq
    refine ⟨Set.mem_image_of_mem f hx₁, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply hmin hx
  have h₂ : Maxima (Set.Icc a b) f = f x₂ := by
    simp only [Maxima]
    apply IsGreatest.csSup_eq
    refine ⟨Set.mem_image_of_mem f hx₂, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    apply hmax hx
  rw [h₁, h₂] at hy
  obtain hle | hle := le_total x₁ x₂
  ·
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hle (hfc.mono (Set.Icc_subset_Icc hx₁.1 hx₂.2)) hy
    exact ⟨x, Set.Icc_subset_Icc hx₁.1 hx₂.2 hx, hfx⟩
  ·
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hle (hfc.mono (Set.Icc_subset_Icc hx₂.1 hx₁.2)) hy
    exact ⟨x, Set.Icc_subset_Icc hx₂.1 hx₁.2 hx, hfx⟩


-- created on 2026-10-08
