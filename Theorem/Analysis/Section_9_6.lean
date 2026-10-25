import Mathlib
import Mathlib.Data.Real.Sign
import Abbrev.Analysis.Section_9_3.Part2
import Theorem.Analysis.Section_9_4.Part2
import Abbrev.Analysis.Section_9_6
/-!
# Analysis I, Section 9.6: The maximum principle

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:
- Continuous functions on closed and bounded intervals are bounded.
- Continuous functions on closed and bounded intervals attain their maximum and minimum.
-/


namespace Chapter9

theorem BddOn.of_bounded {f :ℝ → ℝ} {X: Set ℝ} {M:ℝ} (h: ∀ x ∈ X, |f x| ≤ M) : BddOn f X := by use M

/-- Lemma 9.6.3 -/
theorem BddOn.of_continuous_on_compact {a b:ℝ} (_h:a < b) {f:ℝ → ℝ} (hf: ContinuousOn f (.Icc a b) ) :
  BddOn f (.Icc a b) := by
  -- This proof is written to follow the structure of the original text.
  by_contra! hunbound; simp at hunbound
  set x := fun (n:ℕ) ↦ (hunbound n).choose
  have hx (n:ℕ) : a ≤ x n ∧ x n ≤ b ∧ n < |f (x n)| := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hunbound n).choose_spec; exact ⟨h1, h2, h3⟩
  set X := Set.Icc a b
  observe hXclosed : IsClosed X
  observe hXbounded : Bornology.IsBounded X
  have haX (n:ℕ): x n ∈ X := by simp [X]; specialize hx n; grind
  have ⟨ n, hn, ⟨ L, hLX, hconv ⟩ ⟩ := ((Heine_Borel X).mp ⟨ hXclosed, hXbounded ⟩) x haX
  have why (j:ℕ) : n j ≥ j := why_7_6_3 hn j
  replace hf := hf.continuousWithinAt hLX
  rw [ContinuousWithinAt.iff] at hf
  replace hf := hf.comp (fun j ↦ haX (n j)) hconv
  apply Metric.isBounded_range_of_tendsto at hf
  rw [isBounded_def] at hf; choose M hpos hM using hf
  choose j hj using exists_nat_gt M
  replace hx := (hx (n j)).2.2
  replace hM : f (x (n j)) ∈ Set.Icc (-M) M := by grind
  simp [←abs_le] at hM
  have : n j ≥ (j:ℝ) := by simp [why j]
  linarith

theorem sSup.of_isMaxOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMaxOn f X x₀) :
  sSup (f '' X) = f x₀ := by
  apply IsGreatest.csSup_eq
  simp [IsGreatest, mem_upperBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sInf.of_isMinOn {f:ℝ → ℝ} {X:Set ℝ} {x₀:ℝ} (hx₀: x₀ ∈ X) (h: IsMinOn f X x₀) :
  sInf (f '' X) = f x₀ := by
  apply IsLeast.csInf_eq
  simp [IsLeast, mem_lowerBounds]
  refine ⟨ ⟨x₀, hx₀, rfl ⟩, h ⟩

theorem sSup.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmax ∈ Set.Icc a b, sSup (f '' .Icc a b) = f xmax := by
  choose x hx h' using IsMaxOn.of_continuous_on_compact h hf
  grind [sSup.of_isMaxOn]

theorem sInf.of_continuous_on_compact {a b:ℝ} (h:a < b) (f:ℝ → ℝ) (hf: ContinuousOn f (.Icc a b)) : ∃ xmin ∈ Set.Icc a b, sInf (f '' .Icc a b) = f xmin := by
  choose x hx h' using IsMinOn.of_continuous_on_compact h hf
  grind [sInf.of_isMinOn]

end Chapter9
