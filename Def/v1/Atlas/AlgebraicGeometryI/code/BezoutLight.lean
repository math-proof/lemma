/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutLight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.BezoutLight
set_option maxHeartbeats 400000

open MvPolynomial


/-- Predicate stating that the bivariate polynomial `f ∈ k[X][Y]` has total degree at most `n`,
i.e. for each coefficient `f.coeff i ∈ k[X]` the sum of its `X`-degree and `Y`-index `i` is `≤ n`. -/
def hasTotalDegreeAtMost {k : Type*} [CommSemiring k]
    (f : Polynomial (Polynomial k)) (n : ℕ) : Prop :=
  ∀ i, (f.coeff i).natDegree + i ≤ n

