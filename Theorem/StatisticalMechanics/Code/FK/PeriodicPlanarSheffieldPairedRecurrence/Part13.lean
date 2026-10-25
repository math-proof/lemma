/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part10
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (data : D.ComplementaryCrossNestedLimitCertificate mu) : False := by
  let H0 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (data.a0 n) (data.b0 n)
      (data.c0 n + 4 * data.B) (data.d0 n - 4 * data.B))
  let V1 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (data.a1 n + 4 * data.B) (data.b1 n - 4 * data.B)
      (data.c1 n) (data.d1 n))
  let dualV0 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (data.a0 n + 4 * data.B) (data.b0 n - 4 * data.B)
        (data.c0 n) (data.d0 n))
  let dualH1 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (data.a1 n) (data.b1 n)
        (data.c1 n + 4 * data.B) (data.d1 n - 4 * data.B))
  have hH0sum (n : Nat) : H0 n + dualV0 n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one mu data.Bpos
      data.primalArcBound data.dualArcBound (data.spanX0 n) (data.spanY0 n)
  have hV1sum (n : Nat) : V1 n + dualH1 n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu data.Bpos data.primalArcBound data.dualArcBound
      (data.spanX1 n) (data.spanY1 n)
  have hdualV0 : Tendsto dualV0 atTop (nhds 1) := by
    simpa only [dualV0] using data.dualVertical0
  have hdualH1 : Tendsto dualH1 atTop (nhds 1) := by
    simpa only [dualH1] using data.dualHorizontal1
  have hH0zero : Tendsto H0 atTop (nhds 0) := by
    have hupper (n : Nat) : H0 n <= 1 - dualV0 n := by
      linarith [hH0sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV0
  have hV1zero : Tendsto V1 atTop (nhds 0) := by
    have hupper (n : Nat) : V1 n <= 1 - dualH1 n := by
      linarith [hV1sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH1
  have hmaxZero : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 0) := by
    simpa using hH0zero.max hV1zero
  have hmaxOne : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1) := by
    simpa only [H0, V1] using data.primalAdjacent
  have : (0 : Real) = 1 := tendsto_nhds_unique hmaxZero hmaxOne
  norm_num at this


theorem PeriodicPlanarDualPair.variablePadComplementaryCrossNested_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + pad n) (d0 n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + pad n) (b1 n - pad n) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hdualVertical0 : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n)))
      atTop (nhds 1))
    (hdualHorizontal1 : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n)))
      atTop (nhds 1)) : False := by
  let H0 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + pad n) (d0 n - pad n))
  let V1 : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a1 n + pad n) (b1 n - pad n) (c1 n) (d1 n))
  let dualV0 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n))
  let dualH1 : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n))
  have hH0sum (n : Nat) : H0 n + dualV0 n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_pads mu hBpos
      hBp hBd (hpad n) (hpad n) (hspanX0 n) (hspanY0 n)
  have hV1sum (n : Nat) : V1 n + dualH1 n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads
      mu hBpos hBp hBd (hpad n) (hpad n)
        (hspanX1 n) (hspanY1 n)
  have hH0zero : Tendsto H0 atTop (nhds 0) := by
    have hupper (n : Nat) : H0 n <= 1 - dualV0 n := by
      linarith [hH0sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa [dualV0] using
        (tendsto_const_nhds (x := (1 : Real))).sub hdualVertical0
  have hV1zero : Tendsto V1 atTop (nhds 0) := by
    have hupper (n : Nat) : V1 n <= 1 - dualH1 n := by
      linarith [hV1sum n]
    exact squeeze_zero (fun _ => measureReal_nonneg) hupper <| by
      simpa [dualH1] using
        (tendsto_const_nhds (x := (1 : Real))).sub hdualHorizontal1
  have hmaxZero : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 0) := by
    simpa using hH0zero.max hV1zero
  have hmaxOne : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1) := by
    simpa only [H0, V1] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hmaxZero hmaxOne
  norm_num at this


theorem PeriodicPlanarDualPair.variablePadComplementaryEndpoints_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (hLeft hRight hBottom hTop pad : Nat -> Real)
    (hpad : forall n, 4 * B <= pad n)
    (hspanVX : forall n, vLeft n - pad n + 5 * B <
      vRight n + pad n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanHY : forall n, hBottom n - pad n + 5 * B <
      hTop n + pad n - 5 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (hLeft n + pad n) (hRight n - pad n)
        (hBottom n - pad n) (hTop n + pad n))))
      atTop (nhds 1))
    (hdualVertical : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (vBottom n) (vTop n)))
      atTop (nhds 1))
    (hdualHorizontal : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (hLeft n) (hRight n) (hBottom n) (hTop n)))
      atTop (nhds 1)) : False := by
  apply D.variablePadComplementaryCrossNested_false mu B hBpos hBp hBd
    (fun n => vLeft n - pad n) (fun n => vRight n + pad n)
    vBottom vTop hLeft hRight
    (fun n => hBottom n - pad n) (fun n => hTop n + pad n) pad
    hpad hspanVX hspanVY hspanHX hspanHY
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hprimal
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hdualVertical
  · simpa only [sub_add_cancel, add_sub_cancel_right] using hdualHorizontal


theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (primalEvent : Set (ConfigSpace (Sym2 V)))
    (dualEvent : Set (ConfigSpace (Sym2 W)))
    (hprimal : primalEvent <=
      D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
    (hdual : dualEvent <=
      D.dualEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d) :
    mu.real primalEvent +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
  have hbase := D.matchedCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hp := measureReal_mono (h₂ := measure_ne_top mu _) hprimal
  have hdualPre :
      (dualConfigEquiv D.edgeDual) ⁻¹' dualEvent <=
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a + 4 * B) (b - 4 * B) c d :=
    Set.preimage_mono hdual
  have hd := measureReal_mono (h₂ := measure_ne_top mu _)
    hdualPre
  linarith


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (primalEvent : Set (ConfigSpace (Sym2 V)))
    (dualEvent : Set (ConfigSpace (Sym2 W)))
    (hprimal : primalEvent <=
      D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)
    (hdual : dualEvent <=
      D.dualEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) :
    mu.real primalEvent +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
  have hbase := D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
    mu hBpos hBp hBd hab hcd
  have hp := measureReal_mono (h₂ := measure_ne_top mu _) hprimal
  have hdualPre :
      (dualConfigEquiv D.edgeDual) ⁻¹' dualEvent <=
        (dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            a b (c + 4 * B) (d - 4 * B) :=
    Set.preimage_mono hdual
  have hd := measureReal_mono (h₂ := measure_ne_top mu _)
    hdualPre
  linarith


theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d vLeft vRight : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hleft : a + 4 * B <= vLeft)
    (hright : vRight <= b - 4 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B)) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          vLeft vRight c d) <= 1 := by
  apply D.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.horizontalCrossingEvent
        a b (c + 4 * B) (d - 4 * B))
      (D.dualEmbedding.verticalCrossingEvent vLeft vRight c d)
      (Set.Subset.rfl)
  exact D.dualEmbedding.verticalCrossingEvent_mono_horizontal
    hleft hright


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d hBottom hTop : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hbottom : c + 4 * B <= hBottom)
    (htop : hTop <= d - 4 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b hBottom hTop) <= 1 := by
  apply D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.verticalCrossingEvent
        (a + 4 * B) (b - 4 * B) c d)
      (D.dualEmbedding.horizontalCrossingEvent a b hBottom hTop)
      (Set.Subset.rfl)
  exact D.dualEmbedding.horizontalCrossingEvent_mono_vertical
    hbottom htop


theorem PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerStrips
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d primalBottom primalTop dualLeft dualRight : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hprimalBottom : c + 4 * B <= primalBottom)
    (hprimalTop : primalTop <= d - 4 * B)
    (hdualLeft : a + 4 * B <= dualLeft)
    (hdualRight : dualRight <= b - 4 * B) :
    mu.real (D.primalEmbedding.horizontalCrossingEvent
        a b primalBottom primalTop) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          dualLeft dualRight c d) <= 1 := by
  apply D.matchedCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.horizontalCrossingEvent
        a b primalBottom primalTop)
      (D.dualEmbedding.verticalCrossingEvent dualLeft dualRight c d)
  · exact D.primalEmbedding.horizontalCrossingEvent_mono_vertical
      hprimalBottom hprimalTop
  · exact D.dualEmbedding.verticalCrossingEvent_mono_horizontal
      hdualLeft hdualRight


theorem PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a b c d primalLeft primalRight dualBottom dualTop : Real)
    (hab : a + 5 * B < b - 5 * B)
    (hcd : c + 5 * B < d - 5 * B)
    (hprimalLeft : a + 4 * B <= primalLeft)
    (hprimalRight : primalRight <= b - 4 * B)
    (hdualBottom : c + 4 * B <= dualBottom)
    (hdualTop : dualTop <= d - 4 * B) :
    mu.real (D.primalEmbedding.verticalCrossingEvent
        primalLeft primalRight c d) +
      mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          a b dualBottom dualTop) <= 1 := by
  apply D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets
    mu B hBpos hBp hBd a b c d hab hcd
      (D.primalEmbedding.verticalCrossingEvent
        primalLeft primalRight c d)
      (D.dualEmbedding.horizontalCrossingEvent a b dualBottom dualTop)
  · exact D.primalEmbedding.verticalCrossingEvent_mono_horizontal
      hprimalLeft hprimalRight
  · exact D.dualEmbedding.horizontalCrossingEvent_mono_vertical
      hdualBottom hdualTop


theorem PeriodicPlanarDualPair.horizontalDualVerticalEndpoint_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (dualLeft dualRight dualBottom dualTop : Nat -> Real)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanDVY : forall n, dualBottom n + 5 * B < dualTop n - 5 * B)
    (hBottomFit : forall n, dualBottom n + 4 * B <= hBottom n)
    (hTopFit : forall n, hTop n <= dualTop n - 4 * B)
    (hLeftFit : forall n, hLeft n + 4 * B <= dualLeft n)
    (hRightFit : forall n, dualRight n <= hRight n - 4 * B)
    (hprimal : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1))
    (hdual : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (dualLeft n) (dualRight n) (dualBottom n) (dualTop n)))
      atTop (nhds 1)) : False := by
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))
  have hsum (n : Nat) : H n + dualV n <= 1 :=
    D.matchedCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (hLeft n) (hRight n)
        (dualBottom n) (dualTop n) (hBottom n) (hTop n)
        (dualLeft n) (dualRight n) (hspanHX n) (hspanDVY n)
        (hBottomFit n) (hTopFit n) (hLeftFit n) (hRightFit n)
  have hdual' : Tendsto dualV atTop (nhds 1) := by
    simpa only [dualV] using hdual
  have hzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdual'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hsum n]) hupper
  have hone : Tendsto H atTop (nhds 1) := by
    simpa only [H] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this


theorem PeriodicPlanarDualPair.verticalDualHorizontalEndpoint_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (dualLeft dualRight dualBottom dualTop : Nat -> Real)
    (hspanDHX : forall n, dualLeft n + 5 * B < dualRight n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hLeftFit : forall n, dualLeft n + 4 * B <= vLeft n)
    (hRightFit : forall n, vRight n <= dualRight n - 4 * B)
    (hBottomFit : forall n, vBottom n + 4 * B <= dualBottom n)
    (hTopFit : forall n, dualTop n <= vTop n - 4 * B)
    (hprimal : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1))
    (hdual : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (dualLeft n) (dualRight n) (dualBottom n) (dualTop n)))
      atTop (nhds 1)) : False := by
  let Vcross : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))
  have hsum (n : Nat) : Vcross n + dualH n <= 1 :=
    D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (dualLeft n) (dualRight n)
        (vBottom n) (vTop n) (vLeft n) (vRight n)
        (dualBottom n) (dualTop n) (hspanDHX n) (hspanVY n)
        (hLeftFit n) (hRightFit n) (hBottomFit n) (hTopFit n)
  have hdual' : Tendsto dualH atTop (nhds 1) := by
    simpa only [dualH] using hdual
  have hzero : Tendsto Vcross atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdual'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hsum n]) hupper
  have hone : Tendsto Vcross atTop (nhds 1) := by
    simpa only [Vcross] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this


theorem PeriodicPlanarDualPair.asymmetricEndpointCoordinates_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t -
          D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t -
          D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (vLeft vRight hBottom hTop : Nat -> Real)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hvLeft : forall n, a0 n + 4 * B <= vLeft n)
    (hvRight : forall n, vRight n <= b0 n - 4 * B)
    (hhBottom : forall n, c1 n + 4 * B <= hBottom n)
    (hhTop : forall n, hTop n <= d1 n - 4 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hdualV : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (vLeft n) (vRight n) (c0 n) (d0 n))) atTop (nhds 1))
    (hdualH : Tendsto (fun n => mu.real
      ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (hBottom n) (hTop n))) atTop (nhds 1)) : False := by
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B))
  let V : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (c0 n) (d0 n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (hBottom n) (hTop n))
  have hHdual (n : Nat) : H n + dualV n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip
      mu B hBpos hBp hBd (a0 n) (b0 n) (c0 n) (d0 n)
        (vLeft n) (vRight n) (hspanX0 n) (hspanY0 n)
        (hvLeft n) (hvRight n)
  have hVdual (n : Nat) : V n + dualH n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip
      mu B hBpos hBp hBd (a1 n) (b1 n) (c1 n) (d1 n)
        (hBottom n) (hTop n) (hspanX1 n) (hspanY1 n)
        (hhBottom n) (hhTop n)
  have hdualV' : Tendsto dualV atTop (nhds 1) := by
    simpa only [dualV] using hdualV
  have hdualH' : Tendsto dualH atTop (nhds 1) := by
    simpa only [dualH] using hdualH
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hHdual n]) hupper
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hVdual n]) hupper
  have hzero : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have hone : Tendsto (fun n => max (H n) (V n))
      atTop (nhds 1) := by
    simpa only [H, V] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this


theorem PeriodicPlanarDualPair.fullyAsymmetricEndpointCoordinates_false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (hLeft hRight hBottom hTop : Nat -> Real)
    (vLeft vRight vBottom vTop : Nat -> Real)
    (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
    (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
    (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
    (hspanDVY : forall n,
      dualVBottom n + 5 * B < dualVTop n - 5 * B)
    (hspanDHX : forall n,
      dualHLeft n + 5 * B < dualHRight n - 5 * B)
    (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
    (hHBottom : forall n, dualVBottom n + 4 * B <= hBottom n)
    (hHTop : forall n, hTop n <= dualVTop n - 4 * B)
    (hDVLeft : forall n, hLeft n + 4 * B <= dualVLeft n)
    (hDVRight : forall n, dualVRight n <= hRight n - 4 * B)
    (hVLeft : forall n, dualHLeft n + 4 * B <= vLeft n)
    (hVRight : forall n, vRight n <= dualHRight n - 4 * B)
    (hDHBottom : forall n, vBottom n + 4 * B <= dualHBottom n)
    (hDHTop : forall n, dualHTop n <= vTop n - 4 * B)
    (hprimal : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))))
      atTop (nhds 1))
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
  let H : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))
  let V : Nat -> Real := fun n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  let dualV : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (dualVLeft n) (dualVRight n) (dualVBottom n) (dualVTop n))
  let dualH : Nat -> Real := fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (dualHLeft n) (dualHRight n) (dualHBottom n) (dualHTop n))
  have hHdual (n : Nat) : H n + dualV n <= 1 := by
    exact D.matchedCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (hLeft n) (hRight n)
      (dualVBottom n) (dualVTop n) (hBottom n) (hTop n)
      (dualVLeft n) (dualVRight n) (hspanHX n) (hspanDVY n)
      (hHBottom n) (hHTop n) (hDVLeft n) (hDVRight n)
  have hVdual (n : Nat) : V n + dualH n <= 1 := by
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips
      mu B hBpos hBp hBd (dualHLeft n) (dualHRight n)
      (vBottom n) (vTop n) (vLeft n) (vRight n)
      (dualHBottom n) (dualHTop n) (hspanDHX n) (hspanVY n)
      (hVLeft n) (hVRight n) (hDHBottom n) (hDHTop n)
  have hHzero : Tendsto H atTop (nhds 0) := by
    have hdualV' : Tendsto dualV atTop (nhds 1) := by
      simpa only [dualV] using hdualV
    have hupper : Tendsto (fun n => 1 - dualV n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualV'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hHdual n]) hupper
  have hVzero : Tendsto V atTop (nhds 0) := by
    have hdualH' : Tendsto dualH atTop (nhds 1) := by
      simpa only [dualH] using hdualH
    have hupper : Tendsto (fun n => 1 - dualH n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hdualH'
    exact squeeze_zero (fun _ => measureReal_nonneg)
      (fun n => by linarith [hVdual n]) hupper
  have hzero : Tendsto (fun n => max (H n) (V n)) atTop (nhds 0) := by
    simpa using hHzero.max hVzero
  have hone : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1) := by
    simpa only [H, V] using hprimal
  have : (0 : Real) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this


end StatMech.FK.PeriodicPlanar
