/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPolynomialModule.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.DirectSum.Decomposition
/-!
# Multigraded polynomial modules

This file provides the `ℤⁿ`-graded module interface over a multivariate
polynomial ring `MvPolynomial (Fin n) K` with the standard monomial
degree-shift action. It is the first named dependency towards the
Braun–Davis multigraded Poincaré-series development.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 856–877. Those lines define multigraded free resolutions and
Betti numbers and state that the multigraded Poincaré series of a finitely
generated graded module over a polynomial ring is a polynomial.

Deliberately deferred (not claimed here): multigraded free resolutions,
independence of the Betti numbers, finite support of the Betti table, and
the final polynomiality theorem for the multigraded Poincaré series.
This file only provides the underlying `ℤⁿ`-graded module object with the
monomial degree-shift law on which those later stages will build.

Main definitions:

* `MetaMathlibExt.natDegreeToInt`: embed a monomial exponent `Fin n →₀ ℕ`
  into the `ℤⁿ` grading index.
* `MetaMathlibExt.MultigradedPolynomialModule`: a `K`-submodule
  decomposition of `M` indexed by `Fin n →₀ ℤ`, compatible with scalars via
  `MvPolynomial.C` and shifting under monomial multiplication by the
  embedded exponent degree.
-/


namespace MetaMathlibExt

open MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

/-- Embed a monomial exponent with natural entries into the `ℤⁿ` grading index. -/
noncomputable def natDegreeToInt {n : ℕ} (a : Fin n →₀ ℕ) : Fin n →₀ ℤ :=
  Finsupp.mapRange (fun x : ℕ => (x : ℤ)) (by simp) a

end MetaMathlibExt
