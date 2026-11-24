module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part114
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
