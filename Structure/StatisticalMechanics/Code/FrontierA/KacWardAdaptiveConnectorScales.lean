/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveConnectorScales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveConnectorNeighborhood


namespace StatMech.FrontierA

open scoped BigOperators

structure KWSmallAdaptiveConnectorScales
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) (r : ℝ) where
  beta : ℝ
  alpha : Fin n → ℝ
  hbeta : 0 < beta
  beta_lt_quarter : beta < 1 / 4
  halpha : ∀ i, 0 < alpha i
  alpha_lt_beta : ∀ i, alpha i < beta
  hsum : ∀ i, alpha i + beta < 1
  connector : ∀ i : Fin n, KWAdaptiveConnectorData
    (alpha i * (-polygon.edgeVector (i - 1)))
    (beta * polygon.edgeVector i)
  outgoing_norm_lt : ∀ i : Fin n,
    ‖beta * polygon.edgeVector i‖ < r / 4
  incoming_norm_lt : ∀ i : Fin n,
    ‖alpha i * (-polygon.edgeVector (i - 1))‖ < r / 4

end StatMech.FrontierA
