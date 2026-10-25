/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLocalAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnalyticContinuation.Part2
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem analyticAt_sixVertexBetheResidualGraph
    (N n : Nat) (q : Real × (Fin n → Real)) (hc : 2 < q.1) :
    AnalyticAt Real (sixVertexBetheResidualGraph N n) q := by
  exact analyticAt_fst.prod
    (analyticAt_sixVertexBetheResidual_family N n q hc)


end
end StatMech.FrontierD
