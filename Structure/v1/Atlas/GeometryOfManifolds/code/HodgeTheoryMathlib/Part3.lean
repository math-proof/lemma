/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheoryMathlib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Interval
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheoryMathlib.Part4
set_option autoImplicit false


namespace HodgeMathlib

/-- Data witnessing that $L$ is a linear differential operator of given order with coefficients $a_\alpha$ and local expression $L = \sum_{|\alpha| \le \mathrm{ord}} a_\alpha \partial^\alpha$. -/
structure IsDifferentialOperator {n : ℕ}
    (L : ∀ {k : ℕ}, DiffForm n (k + 1) → DiffForm n (k + 1)) where
  order : ℕ
  coeff : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  coeff_support : ∀ (α : MultiIndex n), multiIndexDegree α > order →
    ∀ {k : ℕ} (ω : DiffForm n (k + 1)), coeff α ω = 0
  partialDeriv : ∀ {k : ℕ}, MultiIndex n → (DiffForm n (k + 1) → DiffForm n (k + 1))
  local_expression : ∀ {k : ℕ} (s : DiffForm n (k + 1)),
    L s = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff α (partialDeriv α s)
  L_add : ∀ {k : ℕ} (α β : DiffForm n (k + 1)), L (α + β) = L α + L β
  L_smul : ∀ {k : ℕ} (r : ℝ) (α : DiffForm n (k + 1)), L (r • α) = r • L α

end HodgeMathlib
