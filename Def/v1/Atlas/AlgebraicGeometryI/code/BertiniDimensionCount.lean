/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage


namespace BertiniArithmetic

/-- Dimension of a generic fiber in the Bertini dimension count: `n - d - 1`. -/
def fiberDim (d n : ℕ) : ℕ := n - d - 1

/-- Dimension of the incidence variety in the Bertini argument: dimension of the base plus the
generic fiber dimension. -/
def incidenceDim (d n : ℕ) : ℕ := d + fiberDim d n

/-- Dimension of the dual projective space `(ℙⁿ)ⱽ` of hyperplanes: `n`. -/
def dualDim (n : ℕ) : ℕ := n

end BertiniArithmetic
