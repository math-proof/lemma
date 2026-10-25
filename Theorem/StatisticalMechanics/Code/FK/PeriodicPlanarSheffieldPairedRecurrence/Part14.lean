/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlanarDualPair.finiteStripArmArrays_dualCrossingLimits_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
    (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n,
      dualVBottom n + 5 * B < dualVTop n - 5 * B)
    (hspanDHX : forall n,
      dualHLeft n + 5 * B < dualHRight n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dualVBottom n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dualVTop n - 4 * B)
    (hDVLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <= dualVLeft n)
    (hDVRight : forall n,
      dualVRight n <= (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dualHLeft n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dualHRight n - 4 * B)
    (hDHBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <= dualHBottom n)
    (hDHTop : forall n,
      dualHTop n <= (vC n + 2 * vD n) / 3 - 4 * B)
    (hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dualVLeft n) (dualVRight n)
          (dualVBottom n) (dualVTop n))) atTop (nhds 1))
    (hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dualHLeft n) (dualHRight n)
          (dualHBottom n) (dualHTop n))) atTop (nhds 1)) : False := by
  have hHorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le hR hC hD hHeight hLower hUpper hgapH
        hHorizontalArms
  have hVertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le vR vC vD vWidth vLower vUpper hgapV
        hVerticalArms
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        ((2 * hC n + hD n) / 3) ((hC n + 2 * hD n) / 3)
        (hR n) (hR n + hHeight n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vR n) (vR n + vWidth n)
        ((2 * vC n + vD n) / 3) ((vC n + 2 * vD n) / 3))))
      atTop (nhds 1) := by
    simpa only [max_self] using hHorizontal.max hVertical
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    (fun n => (2 * hC n + hD n) / 3)
    (fun n => (hC n + 2 * hD n) / 3) hR
    (fun n => hR n + hHeight n) vR (fun n => vR n + vWidth n)
    (fun n => (2 * vC n + vD n) / 3)
    (fun n => (vC n + 2 * vD n) / 3)
    dualVLeft dualVRight dualVBottom dualVTop
    dualHLeft dualHRight dualHBottom dualHTop
    hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop
    hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH


theorem PeriodicPlanarDualPair.finiteStripArmArrays_carriedDual_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
    (hDVLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <= dual.aWide n)
    (hDVRight : forall n,
      dual.bWide n <= (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
    (hDHBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <= dual.cTall n)
    (hDHTop : forall n,
      dual.dTall n <= (vC n + 2 * vD n) / 3 - 4 * B) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  have hHorizontal :=
    D.primalEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le hR hC hD hHeight hLower hUpper hgapH
        hHorizontalArms
  have hVertical :=
    D.primalEmbedding.verticalCrossing_tendsto_one_of_finiteStripJoinedBoundaryArms
      mu B hBp hBpos.le vR vC vD vWidth vLower vUpper hgapV
        hVerticalArms
  have hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        ((2 * hC n + hD n) / 3) ((hC n + 2 * hD n) / 3)
        (hR n) (hR n + hHeight n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vR n) (vR n + vWidth n)
        ((2 * vC n + vD n) / 3) ((vC n + 2 * vD n) / 3))))
      atTop (nhds 1) := by
    simpa only [max_self] using hHorizontal.max hVertical
  have hdualV0 := dual.verticalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualH0 := dual.horizontalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dual.aWide n) (dual.bWide n) (dual.c n) (dual.d n)))
      atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dual.a n) (dual.b n) (dual.cTall n) (dual.dTall n)))
      atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    (fun n => (2 * hC n + hD n) / 3)
    (fun n => (hC n + 2 * hD n) / 3) hR
    (fun n => hR n + hHeight n) vR (fun n => vR n + vWidth n)
    (fun n => (2 * vC n + vD n) / 3)
    (fun n => (vC n + 2 * vD n) / 3)
    dual.aWide dual.bWide dual.c dual.d
    dual.a dual.b dual.cTall dual.dTall
    hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop
    hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH


theorem PeriodicPlanarDualPair.finiteStripArmArrays_reframedCarriedDual_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u -
          D.dualEmbedding.vertex x) i| <= B)
    (hR hC hD : Nat -> Real) (hHeight : Nat -> Nat)
    (hLower hUpper : Nat -> Finset V)
    (vR vC vD : Nat -> Real) (vWidth : Nat -> Nat)
    (vLower vUpper : Nat -> Finset V)
    (hgapH : forall n, 3 * B < hD n - hC n)
    (hgapV : forall n, 3 * B < vD n - vC n)
    (hHorizontalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent
        (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n)))
      atTop (nhds 1))
    (hVerticalArms : Tendsto (fun n => mu.real
      (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent
        (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n)))
      atTop (nhds 1))
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      (2 * hC n + hD n) / 3 + 5 * B <
        (hC n + 2 * hD n) / 3 - 5 * B)
    (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      (2 * vC n + vD n) / 3 + 5 * B <
        (vC n + 2 * vD n) / 3 - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= hR n)
    (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
    (hWideLeft : forall n,
      (2 * hC n + hD n) / 3 + 4 * B <=
        min (dual.a n) (-D.dualEmbedding.orbitBoxCoordinateBound
          (Pdual.bufferedRadius (dual.verticalRadius n)) 0))
    (hWideRight : forall n,
      max (dual.b n) (D.dualEmbedding.orbitBoxCoordinateBound
        (Pdual.bufferedRadius (dual.verticalRadius n)) 0) <=
          (hC n + 2 * hD n) / 3 - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= vR n)
    (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
    (hTallBottom : forall n,
      (2 * vC n + vD n) / 3 + 4 * B <=
        min (dual.c n) (-D.dualEmbedding.orbitBoxCoordinateBound
          (Pdual.bufferedRadius (dual.horizontalRadius n)) 1))
    (hTallTop : forall n,
      max (dual.d n) (D.dualEmbedding.orbitBoxCoordinateBound
        (Pdual.bufferedRadius (dual.horizontalRadius n)) 1) <=
          (vC n + 2 * vD n) / 3 - 4 * B) : False := by
  let reframed := dual.reframeByCoordinateBounds
    D.dualEmbedding (D.dualMeasure mu)
  apply D.finiteStripArmArrays_carriedDual_false mu hFKGDual B hBpos
    hBp hBd hR hC hD hHeight hLower hUpper vR vC vD vWidth
    vLower vUpper hgapH hgapV hHorizontalArms hVerticalArms reframed
  · exact hspanHX
  · exact hspanDVY
  · exact hspanDHX
  · exact hspanVY
  · exact hHBottom
  · exact hHTop
  · exact hWideLeft
  · exact hWideRight
  · exact hVLeft
  · exact hVRight
  · exact hTallBottom
  · exact hTallTop


theorem PeriodicPlanarDualPair.carriedCrossNestedArrays_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hFKGDual : IsFKG (D.dualMeasure mu))
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (primal : D.primalEmbedding.CarriedCrossNestedArray mu)
    (dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu))
    (hspanHX : forall n,
      primal.a n + 5 * B < primal.b n - 5 * B)
    (hspanDVY : forall n,
      dual.c n + 5 * B < dual.d n - 5 * B)
    (hspanDHX : forall n,
      dual.a n + 5 * B < dual.b n - 5 * B)
    (hspanVY : forall n,
      primal.c n + 5 * B < primal.d n - 5 * B)
    (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall n)
    (hHTop : forall n, primal.dTall n <= dual.d n - 4 * B)
    (hDVLeft : forall n, primal.a n + 4 * B <= dual.aWide n)
    (hDVRight : forall n, dual.bWide n <= primal.b n - 4 * B)
    (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide n)
    (hVRight : forall n, primal.bWide n <= dual.b n - 4 * B)
    (hDHBottom : forall n, primal.c n + 4 * B <= dual.cTall n)
    (hDHTop : forall n, dual.dTall n <= primal.d n - 4 * B) : False := by
  letI : IsProbabilityMeasure (D.dualMeasure mu) :=
    inferInstance
  have hprimal := primal.crossingMaxLimit D.primalEmbedding mu hFKG
  have hdualV0 := dual.verticalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualH0 := dual.horizontalCrossingLimit
    D.dualEmbedding (D.dualMeasure mu) hFKGDual
  have hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dual.aWide n) (dual.bWide n) (dual.c n) (dual.d n)))
      atTop (nhds 1) := by
    apply hdualV0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _)]
  have hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dual.a n) (dual.b n) (dual.cTall n) (dual.dTall n)))
      atTop (nhds 1) := by
    apply hdualH0.congr'
    filter_upwards [] with n
    rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]
  exact D.fullyAsymmetricEndpointCoordinates_false mu B hBpos hBp hBd
    primal.a primal.b primal.cTall primal.dTall
    primal.aWide primal.bWide primal.c primal.d
    dual.aWide dual.bWide dual.c dual.d
    dual.a dual.b dual.cTall dual.dTall
    hspanHX hspanDVY hspanDHX hspanVY
    hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop
    hprimal hdualV hdualH


end StatMech.FK.PeriodicPlanar
