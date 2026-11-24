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
public import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part13
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

def
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :
    Prop :=
  ∀ β (hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (FK.boxBdryConnEvent 3 n)
        ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)

set_option linter.style.longLine false in


def FreeQ2BoundaryProfileFiniteFKSimonFreeSumAt
    (β : ℝ) (hβpos : 0 < β) (n : ℕ) : Prop :=
  ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
    : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
      (FK.boxBdryConnEvent 3 n)
    ≤
  ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
    ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)

end Exact3D
end StatMech
