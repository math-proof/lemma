/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example1Summable.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 1

Summability of an alternating rising-factorial series past radius R.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example1Summable

def sector (lam : Option ℝ) (eps : ℝ) (z : ℂ) : Prop :=
  match lam with
  | some l => |Complex.arg (z - (l : ℂ))| ≤ Real.pi / 2 - eps
  | none => |Complex.arg z| ≤ Real.pi - eps
end Section8Example1Summable
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
