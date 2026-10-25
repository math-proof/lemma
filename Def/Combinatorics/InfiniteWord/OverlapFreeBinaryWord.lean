/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/OverlapFreeBinaryWord.lean -/

import Mathlib.Data.List.Basic


namespace MetaMathlibExt

/-!
# Finite overlap-free binary words

Source: J. D. Currie, *The analog of overlap-freeness for the period-doubling sequence*,
Journal of Integer Sequences 26 (2023),
[`currie16.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL26/Currie/currie16.tex).
-/

/-- A word is an overlap if it has the form `x y x y x` for a nonempty word `x`.

Allowing `x` to have arbitrary positive length is essential: restricting it to one letter
does not faithfully state the source definition. -/
def IsWordOverlap {α : Type*} (o : List α) : Prop :=
  ∃ x y : List α, x ≠ [] ∧ o = x ++ y ++ x ++ y ++ x

/-- A finite binary word is overlap-free when none of its contiguous factors is an overlap. -/
def IsOverlapFreeBinaryWord (w : List Bool) : Prop :=
  ∀ o : List Bool, o.IsInfix w → ¬ IsWordOverlap o

end MetaMathlibExt
