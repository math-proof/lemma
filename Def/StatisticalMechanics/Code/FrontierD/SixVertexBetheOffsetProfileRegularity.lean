/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetProfileRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Mathlib.Topology.MetricSpace.Antilipschitz


namespace StatMech.FrontierD

noncomputable section

def sixVertexOffsetCorrectionLipschitzTerm
    (lam : Real) (n : Nat) : Real :=
  (2 / Real.pi) * (n + 1 : Real) *
    Real.exp (-2 * lam) ^ (n + 1)

end
end StatMech.FrontierD
