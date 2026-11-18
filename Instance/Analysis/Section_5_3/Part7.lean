module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Theorem.Analysis.Section_5_3.Part8
public import Theorem.Analysis.Section_5_3.Part7
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

instance Real.instIntCast : IntCast Real where
  intCast n := ((n:ℚ):Real)

noncomputable instance Real.instNeg : Neg Real where
  neg x := ((-1:ℚ):Real) * x

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.addGroup_inst : AddGroup Real :=
  AddGroup.ofLeftAxioms Real.add_assoc (fun a => Real.zero_add a) (fun a => Real.neg_add_cancel a)

/-- Proposition 5.3.11 (laws of algebra) -/
noncomputable instance Real.instCommMonoid : CommMonoid Real where
  mul_assoc := Real.mul_assoc
  one_mul := fun a => Real.one_mul a
  mul_one := fun a => Real.mul_one a
  mul_comm := Real.mul_comm

end Chapter5
