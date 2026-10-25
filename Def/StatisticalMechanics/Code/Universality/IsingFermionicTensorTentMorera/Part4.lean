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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part5


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

noncomputable def reflectedRadialBilinearCellPathIntegral
    (mesh : Real) (a00 a10 a01 a11 : Complex) : Complex :=
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 0 * u) +
    (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 1 y * v) -
    (∫ x : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 x 1 * u) -
    (∫ y : Real in 0..1,
      complexBilinearCell a00 a10 a01 a11 0 y * v)

end
end StatMech.Universality
