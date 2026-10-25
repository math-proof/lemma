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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part4


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

def reflectedRadialBilinearCellContour
    (mesh : Real) (a00 a10 a01 a11 : Complex) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (u * (a00 + a10) + v * (a10 + a11) -
    u * (a01 + a11) - v * (a00 + a01)) / 2

end
end StatMech.Universality
