module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Theorem.Analysis.Section_5_3.Part6
public import Theorem.Analysis.Section_5_1.Part5
@[expose] public section
/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

instance Real.instRatCast : RatCast Real where
  ratCast := fun q ↦
    Quotient.mk _ (CauchySequence.mk' (a := fun _ ↦ q) (by
      rw [Sequence.IsCauchy.coe]
      intro ε hε
      refine ⟨0, ?_⟩
      intro j _ k _
      rw [Section_4_3.dist_eq]
      simpa using le_of_lt hε))

end Chapter5
