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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part10


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_continuous
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh) :=
  finiteCenteredRadialGridInterpolant_continuous n mesh _

@[simp] theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : mesh ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh
        (isingCenteredRadialGridPosition mesh n i.1 j.1) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * mesh) : Complex) :=
  finiteCenteredRadialGridInterpolant_position n mesh hmesh _ i j


theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_projection
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (i j : Fin (2 * n))
    (he : (fkIsingSquareCenteredRadialPatchEdge n i j).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)))
      (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh
        (isingCenteredRadialGridPosition mesh n i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) /
        (Real.sqrt (2 * mesh) : Complex) := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position
    n hn mesh hmesh.ne' i j]
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservable
  exact congrArg (fun z : Complex => z / (Real.sqrt (2 * mesh) : Complex))
    (fkIsingSquareBoundaryFullMedialObservable_projection n hn _ he s)


end
end StatMech.Universality
