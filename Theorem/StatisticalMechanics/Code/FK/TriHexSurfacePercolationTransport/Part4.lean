/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexSurfacePercolationTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusBoundaryReach
import Theorem.StatisticalMechanics.Code.FK.TriHexSurfacePercolationClosure
import Def.StatisticalMechanics.Code.FK.TriHexSurfacePercolationTransport.Part4
open Filter Finset MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem wiredPercolationProbability_eq_of_torusBufferedReachApproximation
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
    triangular.wiredPercolationProbability p q =
      hexagonal.wiredPercolationProbability (BeffaraDC.dualParam p q) q := by
  have htriArm : Tendsto
      (triangularWiredBoundaryArmProbability hp.1 hp.2 hq)
      atTop (nhds (triangular.wiredPercolationProbability p q)) := by
    simpa [triangularWiredBoundaryArmProbability] using
      triangular.bufferedRootBoundaryCylinder_real_tendsto hp.1 hp.2 hq
  have hhexArm : Tendsto
      (hexagonalWiredBoundaryArmProbability hp.1 hp.2 hq)
      atTop (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    simpa [hexagonalWiredBoundaryArmProbability] using
      hexagonal.bufferedRootBoundaryCylinder_real_tendsto
        (BeffaraDC.dualParam_pos hp.1 hp.2 hq)
        (BeffaraDC.dualParam_lt_one hp.1 hp.2 hq) hq
  have htriTorus : Tendsto
      (triangularTorusRadialReachProbability p q) atTop
      (nhds (triangular.wiredPercolationProbability p q)) := by
    have hadd := happrox.1.add htriArm
    convert hadd using 1
    · funext n
      ring
    · simp
  have hhexTorus : Tendsto
      (hexagonalTorusRadialReachProbability p q) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    have hadd := happrox.2.add hhexArm
    convert hadd using 1
    · funext n
      ring
    · simp
  have hhexAsTri : Tendsto
      (triangularTorusRadialReachProbability p q) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (BeffaraDC.dualParam p q) q)) := by
    apply hhexTorus.congr'
    filter_upwards with n
    exact triHexFK_torus_radialReachProbability_eq hq hp hsurface n
  exact tendsto_nhds_unique htriTorus hhexAsTri


theorem triHexSurfacePercolationEquivalence_of_torusBufferedReachApproximation
    {p q : Real} (hq : 0 < q) (hp : p ∈ Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (happrox : TriHexTorusBufferedReachApproximation hp.1 hp.2 hq) :
    TriHexSurfacePercolationEquivalence q p := by
  unfold TriHexSurfacePercolationEquivalence PeriodicGraph.wiredPercolates
  rw [wiredPercolationProbability_eq_of_torusBufferedReachApproximation
    hq hp hsurface happrox]

end
end StatMech.FK.PeriodicPlanar
