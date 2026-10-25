/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

structure FKIsingSquareFullCoordinateOneForm (n : Nat) where
  horizontal : Int × Int -> Real
  vertical : Int × Int -> Real
  closed : ∀ q, FKIsingSquareFullDiamondCell n q ->
    vertical q + horizontal (q.1, q.2 + 1) =
      horizontal q + vertical (q.1 + 1, q.2)

end
end StatMech.Universality
