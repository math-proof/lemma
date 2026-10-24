/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

open Polynomial Finset BigOperators

variable {k : Type*} [Field k]

namespace ResidueSum

/-- The residue of `P/Q` at a simple pole `a`: `P(a) / Q'(a)`, the standard
formula valid when `Q` has a simple root at `a`. -/
noncomputable def residueAtPole (P Q : k[X]) (a : k) : k :=
  P.eval a / Q.derivative.eval a

/-- The product `∏ (X − a_i)` whose roots are the chosen poles, the denominator
of the partial fraction decomposition. -/
noncomputable def poleProd {n : ℕ} (a : Fin n → k) : k[X] :=
  ∏ i : Fin n, (X - C (a i))

/-- The numerator polynomial `Σ_i c_i · ∏_{j ≠ i}(X − a_j)` of a partial-fraction
expression with residues `c_i` at the poles `a_i`. -/
noncomputable def partialFracNumer {n : ℕ} (c a : Fin n → k) : k[X] :=
  ∑ i : Fin n, C (c i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))

/-- The residue at the pole `a_i` of the partial-fraction differential
`partialFracNumer c a / poleProd a`. -/
noncomputable def residuePartialFrac {n : ℕ} (c : Fin n → k) (a : Fin n → k)
    (i : Fin n) : k :=
  residueAtPole (partialFracNumer c a) (poleProd a) (a i)

/-- The residue at infinity of the partial-fraction differential: the negative
of the leading coefficient of the numerator polynomial. -/
noncomputable def residueAtInfPartialFrac {n : ℕ} (c : Fin n → k) (a : Fin n → k) : k :=
  -((partialFracNumer c a).coeff (n - 1))
