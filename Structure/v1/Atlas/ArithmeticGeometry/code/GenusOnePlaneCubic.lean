/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
/-- A smooth projective curve over a field $k$ packaged as: an underlying scheme (with proofs of
integrality, Krull dimension one, nonemptiness), a structure morphism to $\mathrm{Spec}\,k$, and a
(declared) genus value. The smoothness is left implicit. -/
/-- The genus of a smooth projective curve, given by the structural field `genusVal`. -/


namespace SmoothProjectiveCurveOverField

end SmoothProjectiveCurveOverField

noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

/-- A plane cubic over $k$: a nonzero homogeneous polynomial of degree $3$ in three variables. -/
structure PlaneCubic (k : Type*) [Field k] where
  poly : MvPolynomial (Fin 3) k
  isHomogeneous : poly.IsHomogeneous 3
  ne_zero : poly ≠ 0

end
