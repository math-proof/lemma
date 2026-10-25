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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheContinuationProjectionOn
    {a b : Real} {N n : Nat}
    (C : Set (SixVertexBetheContinuationSpace a b N n)) :
    C → Set.Icc a b :=
  fun q => sixVertexBetheContinuationProjection q.1

end
end StatMech.FrontierD
