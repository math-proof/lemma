/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuousOffsetFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierPhysicalDensity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetFourier.Part3


namespace StatMech.FrontierD

open Filter Topology

noncomputable section

def offsetCorrectionMulSinContinuous
    (lam : Real) (n m : Nat) : C(Real, Real) :=
  ⟨fun alpha => sixVertexOffsetCorrectionTerm lam n alpha *
      Real.sin ((m : Real) * alpha), by
    unfold sixVertexOffsetCorrectionTerm
    fun_prop⟩

end
end StatMech.FrontierD
