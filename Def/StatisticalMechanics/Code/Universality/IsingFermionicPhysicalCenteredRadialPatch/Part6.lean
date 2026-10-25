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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part5


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def centeredRadialPatchDualFullFace
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) : FKIsingSquareFullFaceNode n := by
  let q := centeredRadialHalf I J
  have hmod := Nat.not_even_iff.mp hodd
  refine (⟨q - 1, ?_⟩, ⟨n + I - q, ?_⟩)
  · dsimp only [q, centeredRadialHalf]
    omega
  · dsimp only [q, centeredRadialHalf]
    omega

end
end StatMech.Universality
