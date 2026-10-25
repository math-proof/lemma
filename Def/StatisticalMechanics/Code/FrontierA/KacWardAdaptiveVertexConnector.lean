/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveVertexConnector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawSimpleFromEdges


namespace StatMech.FrontierA

open Set


def kwOpenRayTail (a : ℂ) : Set ℂ :=
  {z | ∃ t : ℝ, 1 < t ∧ z = t * a}


def kwHVConnectorCorner (a b : ℂ) : ℂ :=
  b.re + a.im * Complex.I


def kwVHConnectorCorner (a b : ℂ) : ℂ :=
  a.re + b.im * Complex.I

end StatMech.FrontierA
