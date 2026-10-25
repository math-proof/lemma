/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredWeights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem triHexPlanarFiniteTriangleWiredBoundaryProbability_eq
    (n : Nat) {p y q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hodds : p = (1 - p) * y) :
    triHexPlanarFiniteTriangleWiredBoundaryProbability n p q =
      triangleFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  rw [triHexPlanarFiniteTriangleWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n) hp hp1 hq]
  exact triHexPlanarFiniteTriangle_wiredActiveRatio_eq n hp1.ne hodds


theorem triHexPlanarFiniteStarWiredBoundaryProbability_eq
    (n : Nat) {p y q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hodds : p = (1 - p) * y) :
    triHexPlanarFiniteStarWiredBoundaryProbability n p q =
      starFKFiniteWiredBoundaryReachRatio q y y y
        (triHexPlanarFiniteTerminalMap n)
        (triHexPlanarFiniteBoundary n)
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteStarGraph n)
      (triHexPlanarFiniteStarBoundary n) hp hp1 hq]
  exact triHexPlanarFiniteStar_wiredActiveRatio_eq n hp1.ne hodds


theorem triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    triHexPlanarFiniteStarWiredBoundaryProbability n
        (BeffaraDC.dualParam p q) q =
      triHexPlanarFiniteTriangleWiredBoundaryProbability n p q := by
  have hpStar := BeffaraDC.dualParam_mem_Ioo hp.1 hp.2 hq
  have hodds (r : Real) (hr1 : r < 1) :
      r = (1 - r) * FrontierA.fkEdgeOdds r := by
    rw [FrontierA.fkEdgeOdds]
    field_simp [sub_ne_zero.mpr (Ne.symm hr1.ne)]
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq n
      hpStar.1 hpStar.2 hq (hodds _ hpStar.2),
    triHexPlanarFiniteTriangleWiredBoundaryProbability_eq n
      hp.1 hp.2 hq (hodds _ hp.2)]
  exact triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous
    n hq hp hsurface

end
end StatMech.FK.PeriodicPlanar
