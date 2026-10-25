/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

def triHexTorusRadialTarget (n : Nat) :
    Finset (TorusSite (triHexTorusRadialSize n)) := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact Finset.univ.filter fun z =>
    z.1.val = 2 * n + 2 || z.2.val = 2 * n + 2


noncomputable def triangularTorusRadialReachProbability
    (p q : Real) (n : Nat) : Real := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact activeProbOf (triangularTorusGraph (triHexTorusRadialSize n))
    (fun _ => p) q
    (triangularTorusActiveReachEvent (triHexTorusRadialSize n) (0, 0)
      (triHexTorusRadialTarget n))


noncomputable def hexagonalTorusRadialReachProbability
    (p q : Real) (n : Nat) : Real := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact activeProbOf (hexagonalTorusGraph (triHexTorusRadialSize n))
    (fun _ => BeffaraDC.dualParam p q) q
    (hexagonalTorusActiveWhiteReachEvent (triHexTorusRadialSize n) (0, 0)
      (triHexTorusRadialTarget n))


end
end StatMech.FK.PeriodicPlanar
