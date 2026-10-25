/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetNodal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetBoundary
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffsetBound
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetRowContraction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetNodalLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuousOffsetEquation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOffsetNodal


namespace StatMech.FrontierD

open Finset Filter Topology

noncomputable section

def sixVertexCanonicalOffsetNetMargin
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  sixVertexFixedChargeOffsetContractionMargin c -
    sixVertexFixedChargeOffsetRowError c N r lower

end
end StatMech.FrontierD
