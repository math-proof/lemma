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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera


namespace StatMech.Universality

open Filter Set Topology

open scoped BigOperators

noncomputable section

structure VanishingRectangleContourError
    (F : Nat -> Complex -> Complex) where
  error : Complex -> Complex -> Nat -> Real
  error_tendsto_zero : forall z w,
    Tendsto (error z w) atTop (nhds 0)
  contour_norm_le : forall z w n,
    norm (Complex.wedgeIntegral z w (F n) +
      Complex.wedgeIntegral w z (F n)) <= error z w n

end
end StatMech.Universality
