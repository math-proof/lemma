import Mathlib
/-!
# Analysis I, Appendix A.1: Mathematical Statements

An introduction to mathematical statements.  Showcases some basic tactics and Lean syntax.

-/

/- Example A.1.1. What the textbook calls "statements" are objects of type `Prop` in Lean.  Also,
   in Lean we tend to assign "junk" values to expressions that might normally be considered
   undefined, so discussions regarding undefined terms in the textbook should be adjusted
   accordingly. -/   
def Exercise_A_1_3 : Decidable (∀ (X Y: Prop), (X → Y) → (¬X → ¬ Y) → (X ↔ Y)) := by
  --the first line of this construction should be either `apply isTrue` or `apply isFalse`,
  --depending on whether you believe the given statement to be true or false. 
  sorry

/-- Exercise A.1.4. -/
def Exercise_A_1_4 : Decidable (∀ (X Y: Prop), (X → Y) → (¬Y → ¬ X) → (X ↔ Y)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise A.1.5. -/
def Exercise_A_1_5 : Decidable (∀ (X Y Z: Prop), (X ↔ Y) → (Y ↔ Z) → [X,Y,Z].TFAE) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry

/-- Exercise A.1.6. -/
def Exercise_A_1_6 : Decidable (∀ (X Y Z: Prop), (X → Y) → (Y → Z) → (Z → X) → [X,Y,Z].TFAE) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry
