/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanRootControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl
open scoped BigOperators


namespace StatMech.FrontierA

structure NewmanRootCumulantRepresentation
    (cumulants : Nat → Nat → Real) where
  roots : Nat → Nat → Real
  roots_nonneg : ∀ scale i, 0 ≤ roots scale i
  roots_summable : ∀ scale, Summable (roots scale)
  order_zero : ∀ scale, cumulants scale 0 = 0
  odd_order : ∀ scale order, Odd order → cumulants scale order = 0
  even_power_sum : ∀ scale halfOrder, 2 ≤ halfOrder →
    |cumulants scale (2 * halfOrder)| ≤
      (Nat.factorial (2 * halfOrder) : Real) *
        (∑' i, roots scale i ^ halfOrder)
  fourth_mass : ∀ scale,
    12 * (∑' i, roots scale i ^ 2) ≤
      |cumulants scale 4|
  variance_mass : ∀ scale,
    (∑' i, roots scale i) ≤ 1 + |cumulants scale 2|


end StatMech.FrontierA
