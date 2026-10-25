/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDoubledCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDoubledCentralPressure
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexFullWidthRate (c : Real) (k : Nat) : Real :=
  Real.log (sixVertexWidthTopEigenvalue (sixVertexFourWidth 0 k) c) /
    (sixVertexFourWidth 0 k : Real)


noncomputable def sixVertexFullAreaDensity (c : Real) (k M : Nat) : Real :=
  Real.log (sixVertexFixedWidthPartitionSum
    (sixVertexFourWidth 0 k) M c) /
      ((sixVertexFourWidth 0 k : Real) * (M : Real))


end
end StatMech.FrontierD
