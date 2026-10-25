/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgenerating.lean -/

/-
Author: @akiezun, Avocado
-/

import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 9(ii)

Generalized Bell EGF sums to x·e^((a+b)y)·e^(x(e^(by)-1)).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9IiGeneralizedbellgenerating

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

/-- Double-series term: the `n`-th summand of the goal, with the `k`-sum pushed inside. -/
noncomputable def auxTerm (y a b x : ℂ) (n k : ℕ) : ℂ :=
  y ^ n / (Nat.factorial n : ℂ) *
    ((a + b * ((k : ℂ) + 1)) ^ n * x ^ (k + 1) / (Nat.factorial k : ℂ))

/-- Nonnegative majorant for `auxTerm`, used to justify swapping the sums. -/
noncomputable def auxMajor (y a b x : ℂ) (n k : ℕ) : ℝ :=
  ‖y‖ ^ n / (Nat.factorial n : ℝ) *
    ((‖a‖ + ‖b‖ * ((k + 1 : ℕ) : ℝ)) ^ n * ‖x‖ ^ (k + 1) / (Nat.factorial k : ℝ))

end Entry9IiGeneralizedbellgenerating
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
