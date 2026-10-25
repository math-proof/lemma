/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual


namespace StatMech.Universality

open Filter Set Topology

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def isingFiniteWeightedTargetResidual
    {V : Type*} [Fintype V] [Nonempty V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (target : V → Real) : Real := by
  classical
  exact (Finset.univ.image (fun x ↦
    if boundary x then 0 else
      |isingFiniteWeightedLaplacian conductance target x|)).max'
        (Finset.image_nonempty.mpr Finset.univ_nonempty)

end
end StatMech.Universality
