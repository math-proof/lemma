/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPolynomialModule.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.DirectSum.Decomposition
import Def.RingTheory.GradedAlgebra.MultigradedPolynomialModule
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

/-- A `ℤⁿ`-graded module over `MvPolynomial (Fin n) K` with the standard
monomial degree-shift action: each homogeneous piece is a `K`-submodule, the
pieces give a direct-sum decomposition of `M`, scalars act through
`MvPolynomial.C`, and multiplication by `monomial a c` sends the `α`-piece
into the `(α + natDegreeToInt a)`-piece.

This records only the graded object. It does not provide resolutions,
Betti numbers, or any polynomiality conclusion; see the module docstring. -/
structure MultigradedPolynomialModule (M : Type*) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M] where
  /-- The homogeneous `K`-submodule in degree `α`. -/
  component : (Fin n →₀ ℤ) → Submodule K M
  /-- The homogeneous pieces decompose `M` as a direct sum. -/
  decomposition : DirectSum.Decomposition component
  /-- Scalar multiplication by `k : K` agrees with the `MvPolynomial.C k` action. -/
  smul_via_C : ∀ (k : K) (m : M), k • m = ((MvPolynomial.C k : MvPolynomial (Fin n) K)) • m
  /-- Monomials shift homogeneous degrees by the embedded exponent. -/
  monomial_mem : ∀ (a : Fin n →₀ ℕ) (c : K) (α : Fin n →₀ ℤ) (m : M),
    m ∈ component α →
      ((MvPolynomial.monomial a c : MvPolynomial (Fin n) K)) • m ∈
        component (α + natDegreeToInt a)

end MetaMathlibExt
