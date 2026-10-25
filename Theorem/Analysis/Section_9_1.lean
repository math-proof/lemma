import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Abbrev.Analysis.Section_6_4.Part3
import Abbrev.Analysis.Section_9_1
variable (I : Type*)
/-!
# Analysis I, Section 9.1: Subsets of the real line

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib intervals.
- Adherent points, limit points, isolated points.
- Closed sets and closure.
- The Heine-Borel theorem for the real line.

-/


namespace Chapter9

theorem closure_def (X:Set ℝ) : closure X = { x | AdherentPt x X } := by
  ext; simp [Real.mem_closure_iff, AdherentPt, Real.adherent']
  constructor <;> intro h ε hε
  all_goals choose y hy hxy using h _ (half_pos hε); exact ⟨ _, hy, by rw [abs_sub_comm]; linarith ⟩

theorem closure_def' (X:Set ℝ) (x :ℝ) : x ∈ closure X ↔ AdherentPt x X := by
  simp [closure_def]

/-- identification of {name}`AdherentPt` with Mathlib's {name}`ClusterPt` -/
theorem AdherentPt_def (x:ℝ) (X:Set ℝ) : AdherentPt x X = ClusterPt x (.principal X) := by
  rw [←closure_def', mem_closure_iff_clusterPt]

theorem AdherentPt.of_mem {X: Set ℝ} {x: ℝ} (h: x ∈ X) : AdherentPt x X := by
  rw [limit_of_AdherentPt]; use fun _ ↦ x; simp [h]

/-- Definition 9.1.15.  Here we use the Mathlib definition. -/
theorem isClosed_def (X:Set ℝ): IsClosed X ↔ closure X = X :=
  closure_eq_iff_isClosed.symm

theorem isClosed_def' (X:Set ℝ): IsClosed X ↔ ∀ x, AdherentPt x X → x ∈ X := by
  simp [isClosed_def, subset_antisymm_iff, subset_closure]; simp [closure_def]; rfl

/-- Corollary 9.1.17 -/
theorem isClosed_iff_limits_mem (X: Set ℝ) :
  IsClosed X ↔ ∀ (a:ℕ → ℝ) (L:ℝ), (∀ n, a n ∈ X) → Filter.atTop.Tendsto a (nhds L) → L ∈ X := by
  rw [isClosed_def']
  constructor
  . intro h _ L _ _; apply h L; rw [limit_of_AdherentPt]; solve_by_elim
  intro _ _ hx; rw [limit_of_AdherentPt] at hx; grind

end Chapter9
