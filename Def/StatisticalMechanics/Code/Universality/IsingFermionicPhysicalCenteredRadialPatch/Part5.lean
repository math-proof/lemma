/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCenteredRadialPatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservable
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n)) : Complex :=
  fkIsingSquareBoundaryFullMedialObservable n hn
    (fkIsingSquareCenteredRadialPatchEdge n i j)


noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
    (n : Nat) (hn : 0 < n) : Nat -> Nat -> Complex := fun i j =>
  if hi : i < 2 * n then
    if hj : j < 2 * n then
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i, hi⟩ ⟨j, hj⟩
    else 0
  else 0

end
end StatMech.Universality
