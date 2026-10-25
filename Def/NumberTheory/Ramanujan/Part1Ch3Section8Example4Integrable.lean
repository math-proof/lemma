/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Section8Example4Integrable.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.Order.Ring.Star
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 4

Interval integrability of a scaled EGF-type integrand on [0,1].
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example4Integrable

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

/-- `f n x = 1` for `n = -1`, and `f n x = exp (-x) * ∑' j, (j + 1) ^ n * x ^ (j + 1) / j!`,
which is `generalizedBellGenerating 0 1 x n`, otherwise.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 4 and its
correction, printed pp. 51--52 / PDF pp. 61--62. -/
noncomputable def f (n : { n : ℤ // -1 ≤ n }) (x : ℂ) : ℂ :=
  if n.val = -1 then 1 else generalizedBellGenerating 0 1 x n.val.toNat

end Section8Example4Integrable
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
