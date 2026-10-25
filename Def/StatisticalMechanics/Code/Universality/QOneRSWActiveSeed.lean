/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/QOneRSWActiveSeed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWConcreteSeed.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWQOneRectangleCylinder
import Theorem.StatisticalMechanics.Code.Universality.RSWFailureComplementaryArcObstruction.Part8
import Theorem.StatisticalMechanics.Code.Universality.QOneRSWActiveSeed
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.FK

open StatMech.RSW.Box


noncomputable def rq1_adaptiveWiredConnectorEvent {n : ℤ}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  match rlc_axisBarrierGap? gamma gamma' with
  | none => Set.univ
  | some G =>
      if G.lower + 1 = G.upper then
        rlc_mixedAxisGapConnectorEvent G
      else
        rlc_mixedWiredConnectorEvent G

end Universality
end StatMech
