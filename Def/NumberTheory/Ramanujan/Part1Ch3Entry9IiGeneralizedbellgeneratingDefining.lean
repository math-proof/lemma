/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9IiGeneralizedbellgeneratingDefining.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 9(ii)

Generalized-Bell series converges to eˣ times the generating function.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9IiGeneralizedbellgeneratingDefining

/-- Ramanujan's generalized Bell function
`F(a, b, x; n) = e^{-x} ∑_{k ≥ 0} (a + b(k + 1))ⁿ xᵏ⁺¹ / k!`, definition (9.1) of Berndt,
Part I, Chapter 3. -/
noncomputable def generalizedBellGenerating (a b x : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-x) * ∑' (k : ℕ),
      ((a + b * (↑(k + 1) : ℂ)) ^ n * x ^ (k + 1) / (↑(Nat.factorial k) : ℂ))

end Entry9IiGeneralizedbellgeneratingDefining
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
