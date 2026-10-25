import Mathlib
import Theorem.Analysis.Section_4_3.Part2
import Instance.Analysis.Section_5_1
set_option doc.verso.suggestions false

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

/--
Functions from {lean}`ℕ` to {lean}`ℚ` can be thought of as sequences starting from 0; {name}`Sequence.ofNatFun` performs this conversion.

The {attr}`coe` attribute allows the delaborator to print {lean}`Sequence.ofNatFun f` as {lit}`↑f`, which is more concise; you may safely remove this if you prefer the more explicit notation.
-/
@[coe]
def Sequence.ofNatFun (f : ℕ → ℚ) : Sequence where
    n₀ := 0
    seq n := if n ≥ 0 then f n.toNat else 0
    vanish := by grind

end Chapter5
