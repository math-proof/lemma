/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry4.lean -/

/-
Author: @akiezun, Avocado
-/

import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Lemma.Nat.Ramanujan.Part1Ch3Entry4InnerSummable
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 4

Bell-polynomial identity: sum aⁿ/n!·f(x,n-1) equals exp(x(eᵃ-1)).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry4

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

/-- The double-series summand: outer index j, inner index n. -/
noncomputable def T (a x : ℂ) (j n : ℕ) : ℂ :=
  a ^ (n + 1) / ((Nat.factorial (n + 1) : ℕ) : ℂ) *
    (Complex.exp (-x) * (((j + 1 : ℂ)) ^ n * x ^ (j + 1) / (Nat.factorial j : ℂ)))

/-- The outer series. -/
noncomputable def U (a x : ℂ) (n : ℕ) : ℂ :=
  a ^ n / (Nat.factorial n : ℂ) *
    (if n = 0 then (1 : ℂ) else generalizedBellGenerating 0 1 x (n - 1))

end Entry4
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
