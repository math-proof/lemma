/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptivePatchedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple


namespace StatMech.FrontierA

open Set

structure KWAdaptivePatchedData
    {n M : ℕ} [NeZero n] [NeZero M]
    (polygon : KWFiniteSimplePolygon n) where
  data : KWStairParameterData (S := M + 2) polygon
  beta : ℝ
  alpha : Fin n → ℝ
  hM : 2 ≤ M
  hbeta : 0 < beta
  halpha : ∀ i, 0 < alpha i
  hsum : ∀ i, alpha i + beta < 1
  parameter_one : ∀ i,
    data.parameter i (0 : Fin (M + 2)).succ = beta
  parameter_penultimate : ∀ i,
    data.parameter i (Fin.last (M + 1)).castSucc = 1 - alpha (i + 1)
  connector : ∀ i : Fin n, KWAdaptiveConnectorData
    (alpha i * (-polygon.edgeVector (i - 1)))
    (beta * polygon.edgeVector i)

end StatMech.FrontierA
