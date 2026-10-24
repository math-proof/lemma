import Mathlib
import sympy.Basic
open scoped NNReal ENNReal

/--
[uniform_boundedness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/UniformBoundedness.lean)
-/
@[path]
lemma uniform_boundedness
  {A : Type*}
  [NormedAddCommGroup V]
  [NormedSpace ℝ V]
  [CompleteSpace V]
  [NormedAddCommGroup W]
  [NormedSpace ℝ W]
  {T : A → V →L[ℝ] W}
-- given
  (h : ∀ v : V, ∃ C : ℝ, ∀ α : A, ‖T α v‖ ≤ C) :
-- imply
  ∃ C : ℝ, ∀ α : A, ‖T α‖ ≤ C := by
-- proof
  obtain ⟨C, hC⟩ := banach_steinhaus (E := V) (F := W) (g := T) h
  exact ⟨C, hC⟩


-- created on 2026-10-23
-- updated on 2026-10-24
