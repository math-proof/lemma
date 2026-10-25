import Mathlib
import Abbrev.Analysis.Section_3_3_api
import Abbrev.Analysis.Section_3_5.Part9
import Abbrev.Analysis.Section_3_6
/-!
# Analysis I, Section 3.6: Cardinality of sets

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Cardinality of a set
- Finite and infinite sets
- Connections with Mathlib equivalents

After this section, these notions will be deprecated in favor of their Mathlib equivalents.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter3

export SetTheory (Set Object nat)

variable [SetTheory]

/-- Example 3.6.2 -/
theorem SetTheory.Set.Example_3_6_2 : EqualCard {0,1,2} {3,4,5} := by
  classical
  have hne {a b : ℕ} (h : a ≠ b) : (a : Object) ≠ b := by
    intro hab
    exact h ((Object.natCast_inj a b).mp hab)
  let f : ({0,1,2}:Set) → ({3,4,5}:Set) := fun x ↦
    if x.val = 0 then ⟨3, by simp [mem_singleton]⟩
    else if x.val = 1 then ⟨4, by simp [mem_singleton]⟩
    else ⟨5, by simp [mem_singleton]⟩
  refine ⟨f, ⟨?_, ?_⟩⟩
  · intro x y hxy
    have hx : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
      simpa [mem_union, mem_singleton] using x.property
    have hy : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 := by
      simpa [mem_union, mem_singleton] using y.property
    have o01 : (0:Object) ≠ 1 := hne (by decide)
    have o02 : (0:Object) ≠ 2 := hne (by decide)
    have o12 : (1:Object) ≠ 2 := hne (by decide)
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    · exact Subtype.ext (hx.trans hy.symm)
    · simp [f, hx, hy, o01.symm] at hxy
      exact False.elim ((hne (by decide : (3:ℕ) ≠ 4)) hxy)
    · simp [f, hx, hy, o02.symm, o12.symm] at hxy
      exact False.elim ((hne (by decide : (3:ℕ) ≠ 5)) hxy)
    · simp [f, hx, hy, o01.symm] at hxy
      exact False.elim ((hne (by decide : (4:ℕ) ≠ 3)) hxy)
    · exact Subtype.ext (hx.trans hy.symm)
    · simp [f, hx, hy, o01.symm, o02.symm, o12.symm] at hxy
      exact False.elim ((hne (by decide : (4:ℕ) ≠ 5)) hxy)
    · simp [f, hx, hy, o02.symm, o12.symm] at hxy
      exact False.elim ((hne (by decide : (5:ℕ) ≠ 3)) hxy)
    · simp [f, hx, hy, o02.symm, o12.symm, o01.symm] at hxy
      exact False.elim ((hne (by decide : (5:ℕ) ≠ 4)) hxy)
    · exact Subtype.ext (hx.trans hy.symm)
  · intro y
    have hy : y.val = 3 ∨ y.val = 4 ∨ y.val = 5 := by
      simpa [mem_union, mem_singleton] using y.property
    have o01 : (1:Object) ≠ 0 := hne (by decide)
    have o20 : (2:Object) ≠ 0 := hne (by decide)
    have o21 : (2:Object) ≠ 1 := hne (by decide)
    rcases hy with hy | hy | hy
    · exact ⟨⟨0, by simp [mem_singleton]⟩, Subtype.ext (by simp [f, hy])⟩
    · exact ⟨⟨1, by simp [mem_singleton]⟩, Subtype.ext (by simp [f, hy, o01])⟩
    · exact ⟨⟨2, by simp [mem_singleton]⟩, Subtype.ext (by simp [f, hy, o20, o21])⟩

end Chapter3
