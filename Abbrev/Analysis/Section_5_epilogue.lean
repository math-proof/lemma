import Mathlib
import Theorem.Analysis.Section_5_6.Part2
import Theorem.Analysis.Section_5_epilogue
/-!
# Analysis I, Chapter 5 epilogue: Isomorphism with the Mathlib real numbers

In this (technical) epilogue, we show that the "Chapter 5" real numbers {name}`Chapter5.Real` are
isomorphic in various standard senses to the standard real numbers {lean}`ℝ`.  This we do by matching
both structures with Dedekind cuts of the (Mathlib) rational numbers {lean}`ℚ`.

From this point onwards, {name}`Chapter5.Real` will be deprecated, and we will use the standard real
numbers {lean}`ℝ` instead.  In particular, one should use the full Mathlib API for {lean}`ℝ` for all
subsequent chapters, in lieu of the {name}`Chapter5.Real` API.

Filling the {syntax term}`sorry`s here requires both the {name}`Chapter5.Real` API and the Mathlib API for the standard
real numbers {lean}`ℝ`.  As such, they are excellent exercises to prepare you for the aforementioned
transition.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

abbrev Real.toSet_Rat (x:Real) : Set ℚ := { q | (q:Real) < x }

abbrev Real.toCut (x:Real) : DedekindCut :=
 {
   E := x.toSet_Rat
   nonempty := x.toSet_Rat_nonempty
   bounded := x.toSet_Rat_bounded
   lower := x.toSet_Rat_lower
   nomax := x.toSet_Rat_nomax
 }

abbrev DedekindCut.toSet_Real (c: DedekindCut) : Set Real := (fun (q:ℚ) ↦ (q:Real)) '' c.E

noncomputable abbrev DedekindCut.toReal (c: DedekindCut) : Real := sSup c.toSet_Real

end Chapter5
