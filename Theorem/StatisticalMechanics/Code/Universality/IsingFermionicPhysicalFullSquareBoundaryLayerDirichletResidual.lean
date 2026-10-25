/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichlet.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletResidual


namespace StatMech.Universality

open Filter Set Topology

open Finset

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingFiniteWeightedBoundaryError_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (boundary : V → Prop) (data target : V → Real) :
    0 ≤ isingFiniteWeightedBoundaryError boundary data target := by
  classical
  let x : V := Classical.choice inferInstance
  have hx : (if boundary x then |data x - target x| else 0) ≤
      isingFiniteWeightedBoundaryError boundary data target := by
    unfold isingFiniteWeightedBoundaryError
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hzero : 0 ≤ (if boundary x then |data x - target x| else 0) := by
    split_ifs <;> positivity
  exact hzero.trans hx

theorem isingFiniteWeightedBoundaryError_bound
    {V : Type*} [Fintype V] [Nonempty V]
    (boundary : V → Prop) (data target : V → Real)
    (x : V) (hx : boundary x) :
    |data x - target x| ≤
      isingFiniteWeightedBoundaryError boundary data target := by
  classical
  unfold isingFiniteWeightedBoundaryError
  have hmem : |data x - target x| ∈
      Finset.univ.image (fun y ↦
        if boundary y then |data y - target y| else 0) := by
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, by simp [hx]⟩
  exact Finset.le_max' _ _ hmem


end
end StatMech.Universality
