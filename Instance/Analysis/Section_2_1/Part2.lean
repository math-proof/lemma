import Mathlib
import Notation.Analysis.Section_2_1
/-!
# Analysis I, Section 2.1: The Peano Axioms

This file is a translation of Section 2.1 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided doing
so.

Main constructions and results of this section:

- Definition of the "Chapter 2" natural numbers, `Chapter2.Nat`,abbreviated as {name}`Nat` within
  the Chapter2 namespace. (In the book, the natural numbers are treated in a purely axiomatic
  fashion, as a type that obeys the Peano axioms; but here we take advantage of Lean's native
  inductive types to explicitly construct a version of the natural numbers that obey those axioms.
  One could also proceed more axiomatically, as is done in Section 3 for set theory: see the
  epilogue to this chapter.)
- Establishment of the Peano axioms for `Chapter2.Nat`.
- Recursive definitions for `Chapter2.Nat`.

Note: at the end of this chapter, the `Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
`Chapter2.Nat` "by hand" in the next few sections for pedagogical purposes.

-/


namespace Chapter2

instance Nat.instOfNat {n:_root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ n ↦ n++) n

instance Nat.instOne : One Nat := ⟨ 1 ⟩

end Chapter2
