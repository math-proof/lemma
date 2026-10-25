import Abbrev.Analysis.MeasureTheory.Section_1_2_2.Part3
open scoped Pointwise

/-!
# Introduction to Measure Theory, Section 1.2.3: Non-measurable sets

A companion to (the introduction to) Section 1.2.3 of the book "An introduction to Measure Theory".

-/


/-! ## Vitali Set Construction

We construct a Vitali set by choosing representatives from each coset of ℝ/ℚ
that intersects \[0,1\]. The key is that ℚ acts on ℝ by translation, and this
partitions ℝ into countably many disjoint translates of any transversal.
-/

/-- The additive subgroup of ℚ in ℝ -/
def Rat.addSubgroup : AddSubgroup ℝ where
  carrier := Set.range ((↑) : ℚ → ℝ)
  add_mem' := by
    intro a b ⟨qa, ha⟩ ⟨qb, hb⟩
    exact ⟨qa + qb, by simp [ha, hb]⟩
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    intro a ⟨q, hq⟩
    exact ⟨-q, by simp [hq]⟩

