/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 4

Series for (3/2)log 2 - 1 via 2/(64n³-4n).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry4Corollary

noncomputable def H (m : ℕ) : ℝ := ((harmonic m : ℚ) : ℝ)

end Entry4Corollary
end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
