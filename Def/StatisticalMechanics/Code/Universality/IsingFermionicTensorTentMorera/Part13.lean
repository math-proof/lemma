/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTensorTentMorera.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectedTensorTent.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part14


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialAxisSnap (mesh : Real) (z : Complex) : Complex :=
  shiftedRealGridFloor mesh (1 / 2) z.re +
  shiftedRealGridFloor mesh 0 z.im * Complex.I

def reflectedRadialAxisSnapWidth
    (mesh : Real) (z w : Complex) : Nat :=
  shiftedRealGridFloorSteps mesh (1 / 2) z.re w.re

def reflectedRadialAxisSnapHeight
    (mesh : Real) (z w : Complex) : Nat :=
  shiftedRealGridFloorSteps mesh 0 z.im w.im

end
end StatMech.Universality
