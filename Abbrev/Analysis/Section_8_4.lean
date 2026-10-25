import Mathlib
import Theorem.Analysis.Section_8_1.Part4
import Theorem.Analysis.Section_8_2.Part4
set_option doc.verso.suggestions false

/-!
# Analysis I, Section 8.4: The axiom of choice

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Review of Mathlib's dependent product type `∀ α, X α`.
- The axiom of choice in various equivalent forms, as well as the countable axiom of choice.

As the Chapter 3 set theory has been deprecated for many chapters at this point, we will not insert the axiom of choice directly into that theory in this text; but this could be accomplished if desired
(e.g., by extending the `Chapter3.SetTheory` class to a `Chapter3.SetTheoryWithChoice` class), and
students are welcome to attempt this separately.  Instead, we will use Mathlib's native
{name}`Classical.choice` axiom.  Technically, this axiom has already been used quite frequently in the
text already, in large part because Mathlib uses {name}`Classical.choice` to derive many weaker statements,
such as the law of the excluded middle.  So the distinctions made in the original text regarding
whether a given statement or not uses the axiom of choice are somewhat blurred in this formalization.
It is theoretically possible to restore this distinction by removing the reliance on Mathlib and
working throughout with custom structures such as `Chapter3.SetTheory` and
`Chapter3.SetTheoryWithChoice`, but this would be extremely tedious and not attempted here.
-/


namespace Chapter8

/-- Definition 8.4.1 (Infinite Cartesian products).  We will avoid using this definition in favor
of the Mathlib form {lean}`∀ α, X α` which we will shortly show is equivalent to (or more precisely,
generalizes) this one.

{given -show}`α : I`
Because Lean does not allow unrestricted unions of types, we cheat slightly here by assuming all the
{lean}`X α` are sets in a common universe {name}`U`.  Note that the Mathlib definition does not have this
restriction. -/
abbrev CartesianProduct {I U: Type} (X : I → Set U) := { x : I → ⋃ α, X α // ∀ α, ↑(x α) ∈ X α }

end Chapter8
