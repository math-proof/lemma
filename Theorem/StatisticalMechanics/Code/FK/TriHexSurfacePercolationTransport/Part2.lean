/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Def.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part2
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem triHexFK_torus_radialReachProbability_eq
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) (n : Nat) :
    hexagonalTorusRadialReachProbability p q n =
      triangularTorusRadialReachProbability p q n := by
  letI : Fact (2 < triHexTorusRadialSize n) :=
    ⟨triHexTorusRadialSize_gt_two n⟩
  exact triHexFK_torus_homogeneous_activeReachProbability_eq
    (triHexTorusRadialSize n) hq hp hsurface (0, 0)
      (triHexTorusRadialTarget n)


end
end StatMech.FK.PeriodicPlanar
