/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
/-!
# Ramanujan's Notebooks, Part I, Chapter 7: Berndt's `φ_r(x)`

The function `φ_r(x)` of B. C. Berndt, *Ramanujan's Notebooks, Part I* (Springer, 1985),
Chapter 7, shared by several entries of that chapter.
-/


namespace Ramanujan.Part1Ch7

/-- Arguments on which Mathlib's `UnitAddCircle` Hurwitz zeta represents the
ordinary shifted Hurwitz zeta used by Berndt. -/
def Chapter7PhiArgument := Set.Ioo (-1 : ℝ) 0

/-- Berndt's `φ_r(x)`, restricted to `-1 < x < 0`.  On this interval `x + 1`
is the canonical Hurwitz-zeta parameter, so coercion to `UnitAddCircle` does
not introduce the spurious period-one identification present outside it.

Source: Bruce C. Berndt, *Ramanujan's Notebooks, Part I*, Chapter 7,
equation (2.4), p. 152. -/
noncomputable def chapter7Phi (r : ℂ) (x : Chapter7PhiArgument) : ℂ :=
  riemannZeta (-r) -
    HurwitzZeta.hurwitzZeta (((x : ℝ) + 1 : ℝ) : UnitAddCircle) (-r)

end Ramanujan.Part1Ch7
