/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Set


namespace StatMech.FrontierA

def QuantumIsingAlmostAdditive (u : Nat -> Real) (c : Real) : Prop :=
  ∀ m n, |u (m + n) - u m - u n| ≤ c

end StatMech.FrontierA
