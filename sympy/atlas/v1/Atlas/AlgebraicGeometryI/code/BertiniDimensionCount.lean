/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage

namespace BertiniArithmetic

/-- Dimension of a generic fiber in the Bertini dimension count: `n - d - 1`. -/
def fiberDim (d n : ℕ) : ℕ := n - d - 1

/-- Dimension of the incidence variety in the Bertini argument: dimension of the base plus the
generic fiber dimension. -/
def incidenceDim (d n : ℕ) : ℕ := d + fiberDim d n

/-- Dimension of the dual projective space `(ℙⁿ)ⱽ` of hyperplanes: `n`. -/
def dualDim (n : ℕ) : ℕ := n

/-- An abstract bundle of data for a smooth subvariety of `ℙⁿ` of dimension `d` together with
its space of hyperplanes — used to state Bertini's theorem combinatorially. -/
structure SmoothSubvariety where
  n : ℕ
  d : ℕ
  HyperplaneIndex : Type
  hdn : d < n

/-- Opaque predicate: a hyperplane gives a smooth section of `X`. -/
opaque SmoothSubvariety.isSmoothSection (X : SmoothSubvariety) :
    X.HyperplaneIndex → Prop

/-- Bertini's theorem (abstract): for any smooth subvariety `X ⊆ ℙⁿ`, there exists a hyperplane
giving a smooth section (Thm 22.1, Lec 22). -/
structure BertiniThm221 (X : SmoothSubvariety) where
  incidence_dim : X.d + (X.n - X.d - 1) = X.n - 1
  incidence_lt_dual : X.n - 1 < X.n
  smooth_section_exists : ∃ H : X.HyperplaneIndex, X.isSmoothSection H

/-- Builder for `BertiniThm221`, assembling the dimension count and Bertini's smoothness
existence statement. -/
