import Mathlib
import Abbrev.Analysis.Section_3_1_api
import Abbrev.Analysis.Section_3_4.Part6
/-!
# Analysis I, Section 3.4: Images and inverse images

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Images and inverse images of (Mathlib) functions, within the framework of Section 3.1 set
  theory. (The Section 3.3 functions are now deprecated and will not be used further.)
- Connection with Mathlib's image {syntax term}`f '' S` and preimage {syntax term}`f ⁻¹' S` notions.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

theorem SetTheory.Set.iUnion_example : iUnion {1,2,3} index_example = {2,3,4,5} := by
  apply ext
  intro x
  simp only [mem_iUnion, index_example, Insert.insert, mem_union, mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    have hidx : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      have h := i.property
      simpa [mem_union, mem_singleton] using h
    rcases hidx with h1 | h2 | h3
    · simp only [h1, ite_true, mem_union, mem_singleton] at hi
      rcases hi with rfl | rfl
      · left; rfl
      · right; left; rfl
    · have h21 : ¬ ((2:Object) = 1) := by
        intro h
        exact absurd ((Object.natCast_inj 2 1).mp h) (by decide)
      simp only [h2, h21, ite_false, ite_true, mem_union, mem_singleton] at hi
      rcases hi with rfl | rfl
      · right; left; rfl
      · right; right; left; rfl
    · have h31 : ¬ ((3:Object) = 1) := by
        intro h
        exact absurd ((Object.natCast_inj 3 1).mp h) (by decide)
      have h32 : ¬ ((3:Object) = 2) := by
        intro h
        exact absurd ((Object.natCast_inj 3 2).mp h) (by decide)
      simp only [h3, h31, h32, ite_false, mem_union, mem_singleton] at hi
      rcases hi with rfl | rfl
      · right; right; left; rfl
      · right; right; right; rfl
  · intro hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨1, by simp [mem_union, mem_singleton]⟩, by simp [mem_union, mem_singleton]⟩
    · exact ⟨⟨1, by simp [mem_union, mem_singleton]⟩, by simp [mem_union, mem_singleton]⟩
    · have h21 : ¬ ((2:Object) = 1) := by
        intro h
        exact absurd ((Object.natCast_inj 2 1).mp h) (by decide)
      exact ⟨⟨2, by simp [mem_union, mem_singleton]⟩,
        by simp [h21, mem_union, mem_singleton]⟩
    · have h31 : ¬ ((3:Object) = 1) := by
        intro h
        exact absurd ((Object.natCast_inj 3 1).mp h) (by decide)
      have h32 : ¬ ((3:Object) = 2) := by
        intro h
        exact absurd ((Object.natCast_inj 3 2).mp h) (by decide)
      exact ⟨⟨3, by simp [mem_union, mem_singleton]⟩,
        by simp [h31, h32, mem_union, mem_singleton]⟩

/-- Connection with Mathlib indexed union -/
theorem SetTheory.Set.iUnion_eq (I: Set) (A: I → Set) :
    (iUnion I A : _root_.Set Object) = ⋃ α, (A α: _root_.Set Object) := by
  ext; simp [mem_iUnion]

end Chapter3
