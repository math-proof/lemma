/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.Part2


namespace StatMech.Universality

open Filter Set Topology

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingFiniteWeightedTargetResidual_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (target : V → Real) :
    0 ≤ isingFiniteWeightedTargetResidual conductance boundary target := by
  classical
  let x : V := Classical.choice inferInstance
  have hx : (if boundary x then 0 else
      |isingFiniteWeightedLaplacian conductance target x|) ≤
      isingFiniteWeightedTargetResidual conductance boundary target := by
    unfold isingFiniteWeightedTargetResidual
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hzero : 0 ≤ (if boundary x then 0 else
      |isingFiniteWeightedLaplacian conductance target x|) := by
    split_ifs <;> positivity
  exact hzero.trans hx

theorem isingFiniteWeightedTargetResidual_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (conductance : V → V → Real) (boundary : V → Prop)
    (target : V → Real) (x : V) (hx : ¬ boundary x) :
    |isingFiniteWeightedLaplacian conductance target x| ≤
      isingFiniteWeightedTargetResidual conductance boundary target := by
  classical
  unfold isingFiniteWeightedTargetResidual
  have hmem : |isingFiniteWeightedLaplacian conductance target x| ∈
      Finset.univ.image (fun y ↦
        if boundary y then 0 else
          |isingFiniteWeightedLaplacian conductance target y|) := by
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simp [hx]⟩
  exact Finset.le_max' _ _ hmem

end
end StatMech.Universality
