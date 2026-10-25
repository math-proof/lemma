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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part9


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem finiteCenteredRadialGridInterpolant_continuous
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
    Continuous (finiteCenteredRadialGridInterpolant n mesh value) := by
  exact (finiteRadialGridInterpolant_continuous (2 * n) mesh value).comp
    (continuous_id.add continuous_const)

@[simp] theorem finiteCenteredRadialGridInterpolant_position
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Fin (2 * n)) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridPosition mesh n i.1 j.1) = value i j := by
  unfold finiteCenteredRadialGridInterpolant isingCenteredRadialGridPosition
  rw [sub_add_cancel]
  exact finiteRadialGridInterpolant_position (2 * n) mesh hmesh value i j

theorem finiteCenteredRadialGridInterpolant_cellPoint
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      complexBilinearCell
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
  unfold finiteCenteredRadialGridInterpolant isingCenteredRadialGridCellPoint
  rw [sub_add_cancel]
  exact finiteRadialGridInterpolant_cellPoint mesh hmesh value i j hi hj
    x y hx0 hx1 hy0 hy1


end
end StatMech.Universality
