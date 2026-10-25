/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.CellDecomposition
open Finset Set MvPolynomial


namespace CellDecomposition

/-- Membership of a point in a `Line2`: belongs to the underlying affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier


end CellDecomposition
