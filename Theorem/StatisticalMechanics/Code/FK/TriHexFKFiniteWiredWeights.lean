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
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights
open Finset Set
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section

theorem wiredActiveRatio_eq_wiredFkProb_lift
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (boundary : V -> Prop) [DecidablePred boundary]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (observable : ConfigSpace G.edgeSet -> Real) :
    wiredActiveRatio G boundary p q observable =
      ∑ omega : ConfigSpace (Sym2 V),
        observable (restrictActive G omega) *
          wiredFkProb G boundary p q omega := by
  rw [← activeBCMean_boundaryClique_eq_wired G boundary hp hp1 hq]
  rw [activeBCMean_eq_div]
  unfold wiredActiveRatio wiredActiveNumer wiredActiveZ wiredActiveWeight
    activeBCNumer activeBCZ activeBCWeight wiredFkWeight
  simp only [numClustersBC_boundaryClique]
  rfl


theorem triHexPlanarFiniteTriangle_localOddsProduct
    (n : Nat) (y : Real)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    (∏ z, triangleFKLocalOddsWeight y y y
      (triHexPlanarFiniteTriangleConfigEquiv n omega z)) =
      ∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet,
        if omega e then y else 1 := by
  rw [triangleFKGlobalLocalOdds_eq_directionProduct]
  calc
    (∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if triHexLocalDirection
            (triHexPlanarFiniteTriangleConfigEquiv n omega a.1) a.2 then
          triHexDirectionOdds y y y a.2 else 1) =
      ∏ a : TriHexPlanarFiniteCell n × Fin 3,
        if omega (triHexPlanarFiniteTriangleEdgeEquiv n a) then y else 1 := by
          apply Fintype.prod_congr
          rintro ⟨z, i⟩
          fin_cases i <;> rfl
    _ = ∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet,
        if omega e then y else 1 := by
      simpa using (triHexPlanarFiniteTriangleEdgeEquiv n).prod_comp
        (fun e => if omega e then y else 1)


theorem triHexPlanarFiniteTriangle_edgeProduct
    (n : Nat) {p y : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    edgeProduct (triHexPlanarFiniteTriangleGraph n) p
        (extendActive (triHexPlanarFiniteTriangleGraph n) omega) =
      (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        ∏ z, triangleFKLocalOddsWeight y y y
          (triHexPlanarFiniteTriangleConfigEquiv n omega z) := by
  change edgeProductW (triHexPlanarFiniteTriangleGraph n) (fun _ => p)
      (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = _
  rw [edgeProductW_extendActive_odds_factor
    (triHexPlanarFiniteTriangleGraph n) (fun _ => p) (fun _ => y)
    (fun _ => hodds)]
  rw [triHexPlanarFiniteTriangle_localOddsProduct]


theorem triHexPlanarFiniteTriangle_wiredActiveWeight_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y)
    (omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet) :
    wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q omega =
      (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)
            (fun z => triangleFKLocalConnectivity
              (triHexPlanarFiniteTriangleConfigEquiv n omega z)) *
          ∏ z, triangleFKLocalOddsWeight y y y
            (triHexPlanarFiniteTriangleConfigEquiv n omega z)) := by
  unfold wiredActiveWeight wiredFkWeight
  rw [triHexPlanarFiniteTriangle_edgeProduct n hodds,
    triHexPlanarFiniteTriangle_numClustersWired_eq_sector]
  unfold triHexFKTerminalWiredExternal
    triHexPlanarFiniteTriangleWiredSectorGraph
  ring


theorem triHexPlanarFiniteTriangle_wiredActiveZ_eq
    (n : Nat) {p y q : Real} (hodds : p = (1 - p) * y) :
    wiredActiveZ (triHexPlanarFiniteTriangleGraph n)
        (triHexPlanarFiniteBoundary n) p q =
      (∏ e : (triHexPlanarFiniteTriangleGraph n).edgeSet, (1 - p)) *
        triangleFKGlobalConfigSum y y y
          (triHexFKTerminalWiredExternal q
            (triHexPlanarFiniteTerminalMap n)
            (triHexPlanarFiniteBoundary n)) := by
  classical
  unfold wiredActiveZ triangleFKGlobalConfigSum
  rw [← (triHexPlanarFiniteTriangleConfigEquiv n).symm.sum_comp
    (fun omega => wiredActiveWeight (triHexPlanarFiniteTriangleGraph n)
      (triHexPlanarFiniteBoundary n) p q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triHexPlanarFiniteTriangle_wiredActiveWeight_eq n hodds]
  rw [(triHexPlanarFiniteTriangleConfigEquiv n).apply_symm_apply config]


end
end StatMech.FK.PeriodicPlanar
