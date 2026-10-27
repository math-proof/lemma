import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


namespace AdditiveCombinatorics

/--
[Finset.card_sub_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/RuzsaTriangle.lean)
-/
@[path]
lemma Finset.card_sub_comm
  [DecidableEq G]
  [AddCommGroup G]
  {A B : Finset G} :
-- imply
  (B - A).card = (A - B).card := by
-- proof
  have h : B - A = -(A - B) := by
    ext x
    simp only [Finset.mem_neg, Finset.mem_sub]
    constructor
    · rintro ⟨b, hb, a, ha, rfl⟩
      exact ⟨a - b, ⟨a, ha, b, hb, rfl⟩, by simp [neg_sub]⟩
    · rintro ⟨y, ⟨a, ha, b, hb, rfl⟩, hy⟩
      exact ⟨b, hb, a, ha, by rw [← hy]; simp [neg_sub]⟩
  rw [h, Finset.card_neg]

end AdditiveCombinatorics

namespace AdditiveCombinatorics

/--
[Finset.ruzsa_triangle_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/RuzsaTriangle.lean)
-/
@[path]
lemma Finset.ruzsa_triangle_inequality
  [DecidableEq G]
  [AddCommGroup G]
  {A B C : Finset G} :
-- imply
  A.card * (B - C).card ≤ (A - B).card * (A - C).card := by
-- proof
  have h := _root_.Finset.ruzsa_triangle_inequality_sub_sub_sub B A C
  rw [mul_comm] at h
  rwa [Finset.card_sub_comm A B, Finset.card_sub_comm A C] at h

end AdditiveCombinatorics


-- created on 2026-10-23
