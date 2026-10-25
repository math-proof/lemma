/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HenselsLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.Hensel


noncomputable section

open Polynomial

section DoubleRoot

/-- Definition 8.6 (formal derivative): for a polynomial $f \in R[X]$ over a commutative semiring,
the formal derivative $f'$ is the polynomial obtained term-by-term. Thin abbreviation for
`Polynomial.derivative`. -/
abbrev formalDerivative {R : Type*} [CommSemiring R] (f : R[X]) : R[X] :=
  Polynomial.derivative f

end DoubleRoot
end
