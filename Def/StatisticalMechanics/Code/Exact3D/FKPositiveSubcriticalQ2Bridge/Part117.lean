/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part114
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

def boxSymId (d : ℕ) : FK.BoxSym d where
  τ := Equiv.refl (Lattice.Site d)
  adj := by
    intro _ _
    rfl
  box_mem := by
    intro _ _
    rfl


def boxSymComp {d : ℕ} (S T : FK.BoxSym d) : FK.BoxSym d where
  τ := T.τ.trans S.τ
  adj := by
    intro x y
    change (Lattice.hypercubicLattice d).Adj (S.τ (T.τ x)) (S.τ (T.τ y)) ↔
      (Lattice.hypercubicLattice d).Adj x y
    rw [S.adj, T.adj]
  box_mem := by
    intro n x
    change S.τ (T.τ x) ∈ Lattice.box d n ↔ x ∈ Lattice.box d n
    rw [S.box_mem, T.box_mem]


def transverseAbsBoxSym3 (x : Lattice.Site 3) : FK.BoxSym 3 :=
  boxSymComp
    (if 0 ≤ x (2 : Fin 3) then boxSymId 3 else FK.fkTI_signFlip 3 (2 : Fin 3))
    (if 0 ≤ x (1 : Fin 3) then boxSymId 3 else FK.fkTI_signFlip 3 (1 : Fin 3))


end Exact3D
end StatMech
