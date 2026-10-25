import Mathlib
import Mathlib.Analysis.SpecificLimits.Basic
import Abbrev.Analysis.Section_6_4.Part3
import Abbrev.Analysis.Section_9_1.Part3
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

theorem LimitPt.iff_limit (x:ℝ) (X: Set ℝ) :
  LimitPt x X ↔ ∃ a : ℕ → ℝ, (∀ n, a n ∈ X \ {x}) ∧ Filter.atTop.Tendsto a (nhds x) := by
  simp [limit_of_AdherentPt]

/-- Definition 9.1.22.  We use here Mathlib's {name}`Bornology.IsBounded` -/

theorem isBounded_def (X: Set ℝ) : Bornology.IsBounded X ↔ ∃ M > 0, X ⊆ .Icc (-M) M := by
  simp [isBounded_iff_forall_norm_le]
  constructor
  . intro ⟨ C, hC ⟩; use (max C 1)
    refine ⟨ lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_ ⟩
    peel hC with x hx hC; rw [abs_le'] at hC; simp [hC.1]; linarith [le_max_left C 1]
  intro ⟨ M, hM, hXM ⟩; use M; intro x hx; specialize hXM hx; simp_all [abs_le']; linarith [hXM.1]

end Chapter9
