/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part2
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem TriHexFiniteWiredLevel.starBoundaryReachRatio_eq_triangle
    (D : TriHexFiniteWiredLevel) {q p : Real}
    (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    D.starBoundaryReachRatio q p = D.triangleBoundaryReachRatio q p := by
  letI := D.cellFintype
  letI := D.cellDecidableEq
  letI := D.vertexFintype
  letI := D.vertexDecidableEq
  letI := D.boundaryDecidable
  exact triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous
    hq hp hsurface D.terminal D.boundary D.root


theorem triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous
    (D : Nat → TriHexFiniteWiredLevel) {q p theta : Real}
    (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    Filter.Tendsto (fun n => (D n).starBoundaryReachRatio q p)
        Filter.atTop (nhds theta) ↔
      Filter.Tendsto (fun n => (D n).triangleBoundaryReachRatio q p)
        Filter.atTop (nhds theta) := by
  have hseq : (fun n => (D n).starBoundaryReachRatio q p) =
      fun n => (D n).triangleBoundaryReachRatio q p := by
    funext n
    exact (D n).starBoundaryReachRatio_eq_triangle hq hp hsurface
  rw [hseq]


end
end StatMech.FK.PeriodicPlanar
