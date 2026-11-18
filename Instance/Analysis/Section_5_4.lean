module

public import Mathlib
public import Theorem.Analysis.Section_5_3.Part12
public import Theorem.Analysis.Section_5_4.Part3
@[expose] public section
/-!
# Analysis I, Section 5.4: Ordering the reals

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Ordering on the real line

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLT : LT Real where
  lt x y := (x-y).IsNeg

/-- Definition 5.4.6 (Ordering of the reals) -/
instance Real.instLE : LE Real where
  le x y := (x < y) ∨ (x = y)


open Classical in
/-- (Not from textbook) `Real` has the structure of a linear ordering. The order is not
computable, and so classical logic is required to impose decidability. -/
noncomputable instance Real.instLinearOrder : LinearOrder Real where
  le_refl := fun x => Or.inr rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with hxy | rfl
    · rcases hyz with hyz | rfl
      · left
        have h1 : (y - x).IsPos := by
          rw [← neg_sub x y]
          exact (Real.neg_iff_pos_of_neg (x - y)).mp hxy
        have h2 : (z - y).IsPos := by
          rw [← neg_sub y z]
          exact (Real.neg_iff_pos_of_neg (y - z)).mp hyz
        have hzx : (z - x).IsPos := by
          have : z - x = (z - y) + (y - x) := by
            rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_assoc,
                ← add_assoc (-y), _root_.neg_add_cancel, _root_.zero_add]
          rw [this]
          exact Real.pos_add h2 h1
        exact (Real.neg_iff_pos_of_neg (x - z)).mpr (by rwa [neg_sub])
      · left; exact hxy
    · exact hyz
  lt_iff_le_not_ge := by
    intro x y
    constructor
    · intro hxy
      refine ⟨Or.inl hxy, ?_⟩
      intro hyx
      rcases hyx with hyx | hyx
      · have hypos : (y - x).IsPos := by
          rw [← neg_sub x y]
          exact (Real.neg_iff_pos_of_neg (x - y)).mp hxy
        exact (Real.not_pos_neg (y - x) ⟨hypos, hyx⟩).elim
      · have : x - y = 0 := sub_eq_zero.mpr hyx.symm
        exact (Real.not_zero_neg (x - y)) ⟨this, hxy⟩
    · intro h
      rcases h.1 with hlt | heq
      · exact hlt
      · exact (h.2 (Or.inr heq.symm)).elim
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with hxy | rfl
    · rcases hyx with hyx | hyx
      · have hypos : (y - x).IsPos := by
          rw [← neg_sub x y]
          exact (Real.neg_iff_pos_of_neg (x - y)).mp hxy
        exact (Real.not_pos_neg (y - x) ⟨hypos, hyx⟩).elim
      · exact hyx.symm
    · rfl
  le_total := by
    intro x y
    rcases Real.trichotomous (x - y) with h0 | hp | hn
    · left; right; exact sub_eq_zero.mp h0
    · right; left
      have : (y - x).IsNeg := by
        exact (Real.neg_iff_pos_of_neg (y - x)).mpr (by rwa [neg_sub])
      exact this
    · left; left; exact hn
  toDecidableLE := Classical.decRel _

end Chapter5
