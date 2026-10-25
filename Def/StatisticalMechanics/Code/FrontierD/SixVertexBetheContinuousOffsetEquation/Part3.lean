/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetEquation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffset.Part2
import Mathlib.Analysis.Calculus.SmoothSeries
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part2


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def XiFourierTermMulOffsetRapidityProfileContinuous
    {lam : Real} (hlam : 0 < lam) (n : Nat) (alpha : Real) : C(Real, Real) :=
  ⟨fun beta => sixVertexXiFourierTerm (2 * lam) n (alpha - beta) *
      sixVertexOffsetRapidityProfile lam beta, by
    exact (by
      unfold sixVertexXiFourierTerm
      fun_prop : Continuous _).mul
        (continuous_sixVertexOffsetRapidityProfile hlam)⟩


end
end StatMech.FrontierD
