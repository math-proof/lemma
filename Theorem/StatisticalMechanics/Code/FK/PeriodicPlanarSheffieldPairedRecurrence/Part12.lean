/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part9
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
    (f0 f1 f2 f3 f4 : Nat -> Nat -> Real)
    (hf0 : forall k, Tendsto (f0 k) atTop (nhds 1))
    (hf1 : forall k, Tendsto (f1 k) atTop (nhds 1))
    (hf2 : forall k, Tendsto (f2 k) atTop (nhds 1))
    (hf3 : forall k, Tendsto (f3 k) atTop (nhds 1))
    (hf4 : forall k, Tendsto (f4 k) atTop (nhds 1))
    (hle0 : forall k n, f0 k n <= 1)
    (hle1 : forall k n, f1 k n <= 1)
    (hle2 : forall k n, f2 k n <= 1)
    (hle3 : forall k n, f3 k n <= 1)
    (hle4 : forall k n, f4 k n <= 1) :
    exists index : Nat -> Nat,
      (forall n, n <= index n) /\
      forall k : Nat -> Nat, (forall n, k n < n + 1) ->
        Tendsto (fun n => f0 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f1 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f2 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f3 (k n) (index n)) atTop (nhds 1) /\
        Tendsto (fun n => f4 (k n) (index n)) atTop (nhds 1) := by
  let combined : Nat -> Nat -> Real := fun k n =>
    min (f0 k n) (min (f1 k n)
      (min (f2 k n) (min (f3 k n) (f4 k n))))
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hf0 k).min ((hf1 k).min ((hf2 k).min ((hf3 k).min (hf4 k))))
  have hcombinedLe (k n : Nat) : combined k n <= 1 :=
    (min_le_left _ _).trans (hle0 k n)
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  refine ⟨index, hindex, ?_⟩
  intro k hk
  have hlimit := huniform k hk
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => min_le_left _ _) (fun n => hle0 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_left _ _))
      (fun n => hle1 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      (fun n => hle2 (k n) (index n)), ?_⟩
  refine ⟨hlimit.squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans
        ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))))
      (fun n => hle3 (k n) (index n)), ?_⟩
  exact hlimit.squeeze tendsto_const_nhds
    (fun n => (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))))
    (fun n => hle4 (k n) (index n))


theorem PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.toRecursive
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseRecursiveRectangleArrayCertificate mu) :
    Nonempty (D.RecursiveRectangleArrayCertificate mu) := by
  let horizontal : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (raw.a (k + 1) n) (raw.b (k + 1) n)
      (raw.c (k + 1) n + 4 * raw.B) (raw.d (k + 1) n - 4 * raw.B))
  let primal : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (raw.a k n) (raw.b k n)
      (raw.c k n + 4 * raw.B) (raw.d k n - 4 * raw.B)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (raw.a (k + 1) n + 4 * raw.B) (raw.b (k + 1) n - 4 * raw.B)
      (raw.c (k + 1) n) (raw.d (k + 1) n)))
  let dual : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (raw.a k n + 4 * raw.B) (raw.b k n - 4 * raw.B)
        (raw.c k n) (raw.d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (raw.a k n) (raw.b k n)
        (raw.c k n + 4 * raw.B) (raw.d k n - 4 * raw.B)))
  let combined : Nat -> Nat -> Real := fun k n =>
    min (horizontal k n) (min (primal k n) (dual k n))
  have hhorizontal (k : Nat) : Tendsto (horizontal k) atTop (nhds 1) := by
    simpa only [horizontal] using raw.horizontalLevel k
  have hprimal (k : Nat) : Tendsto (primal k) atTop (nhds 1) := by
    simpa only [primal] using raw.primalLevel k
  have hdual (k : Nat) : Tendsto (dual k) atTop (nhds 1) := by
    simpa only [dual] using raw.dualLevel k
  have hcombined (k : Nat) : Tendsto (combined k) atTop (nhds 1) := by
    simpa only [combined, min_self] using
      (hhorizontal k).min ((hprimal k).min (hdual k))
  have hcombinedLe (k n : Nat) : combined k n <= 1 :=
    (min_le_left _ _).trans measureReal_le_one
  obtain ⟨index, hindex, huniform⟩ :=
    exists_cofinalIndex_uniform_tendsto_one_below_diagonal
      combined hcombined hcombinedLe
  have hindexTop : Tendsto index atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hn.trans (hindex n)
  let K : Nat -> Nat := fun n => n.pred
  let a : Nat -> Nat -> Real := fun n k => raw.a k (index n)
  let b : Nat -> Nat -> Real := fun n k => raw.b k (index n)
  let c : Nat -> Nat -> Real := fun n k => raw.c k (index n)
  let d : Nat -> Nat -> Real := fun n k => raw.d k (index n)
  have hcomponentLimit (k : Nat -> Nat) (hk : forall n, k n < n + 1) :
      Tendsto (fun n => combined (k n) (index n)) atTop (nhds 1) :=
    huniform k hk
  have hhorizontalOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => horizontal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => min_le_left _ _) (fun _ => measureReal_le_one)
  have hprimalOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => primal (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_left _ _))
      (fun _ => max_le measureReal_le_one measureReal_le_one)
  have hdualOfCombined (k : Nat -> Nat)
      (hk : forall n, k n < n + 1) :
      Tendsto (fun n => dual (k n) (index n)) atTop (nhds 1) :=
    (hcomponentLimit k hk).squeeze tendsto_const_nhds
      (fun n => (min_le_right _ _).trans (min_le_right _ _))
      (fun _ => max_le measureReal_le_one measureReal_le_one)
  refine ⟨{
    B := raw.B
    Bpos := raw.Bpos
    primalArcBound := raw.primalArcBound
    dualArcBound := raw.dualArcBound
    a := a
    b := b
    c := c
    d := d
    K := K
    spanX := fun n k => raw.spanX k (index n)
    spanY := fun n k => raw.spanY k (index n)
    verticalStart := raw.verticalStart.comp hindexTop
    horizontalEnd := ?_
    primalAdjacent := ?_
    dualLevels := ?_ }⟩
  · have hK : forall n, K n < n + 1 := by
      intro n
      exact (Nat.pred_le n).trans_lt (Nat.lt_succ_self n)
    have hlim := hhorizontalOfCombined K hK
    simpa only [horizontal, a, b, c, d] using hlim
  · intro k hk
    have hk' : forall n, k n < n + 1 := by
      intro n
      exact (hk n).trans_le (Nat.succ_le_succ (Nat.pred_le n))
    have hlim := hprimalOfCombined k hk'
    simpa only [primal, a, b, c, d] using hlim
  · intro k hk
    let k' : Nat -> Nat := fun n => if n = 0 then 0 else k n
    have hk' : forall n, k' n < n + 1 := by
      intro n
      by_cases hn : n = 0
      · simp [k', hn]
      · have hkn := hk n
        have hp : n.pred + 1 = n := by
          simpa only [Nat.succ_eq_add_one] using Nat.succ_pred hn
        dsimp only [K] at hkn
        rw [hp] at hkn
        simpa [k', hn] using Nat.lt_succ_of_le hkn
    have hlim := hdualOfCombined k' hk'
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simpa [dual, a, b, c, d, k', hn0]


theorem PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (raw : D.PointwiseRecursiveRectangleArrayCertificate mu) : False := by
  obtain ⟨bounded⟩ := raw.toRecursive D mu
  exact bounded.false D mu


theorem PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
      atTop (nhds 1))
    (hhorizontalLevel : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
      atTop (nhds 1))
    (hnormalAdjacent : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hrotatedDualLevel : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
      atTop (nhds 1)) : False := by
  exact PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false
    D mu {
      B := B
      Bpos := hBpos
      primalArcBound := hBp
      dualArcBound := hBd
      a := a
      b := b
      c := c
      d := d
      spanX := hspanX
      spanY := hspanY
      verticalStart := hverticalStart
      horizontalLevel := hhorizontalLevel
      primalLevel := hnormalAdjacent
      dualLevel := hrotatedDualLevel }


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d : Nat -> Nat -> Real)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hverticalStart :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n)))
        atTop (nhds 1))
    (hhorizontalLevel :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a (k + 1) n) (b (k + 1) n)
          (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B)))
        atTop (nhds 1))
    (hnormalAdjacent :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B)
          (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hrotatedDualLevel :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hverticalStart hhorizontalLevel hnormalAdjacent
  dsimp only at hrotatedDualLevel
  dsimp only
  intro _hcommon
  exact D.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits
    _ B hBpos hBp hBd a b c d hspanX hspanY hverticalStart
    hhorizontalLevel hnormalAdjacent hrotatedDualLevel


theorem PeriodicPlanarDualPair.dualMeasure_crossingMax_tendsto_one
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (aV bV cV dV aH bH cH dH : Nat -> Real)
    (hlimit : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (aV n) (bV n) (cV n) (dV n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (aV n) (bV n) (cV n) (dV n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1) := by
  apply hlimit.congr'
  filter_upwards [] with n
  rw [D.dualMeasure_measureReal mu
      (D.dualEmbedding.verticalCrossingEvent_measurableSet _ _ _ _),
    D.dualMeasure_measureReal mu
      (D.dualEmbedding.horizontalCrossingEvent_measurableSet _ _ _ _)]


theorem PeriodicPlanarDualPair.dualMeasure_twoLevel_outward_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hdual0 : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1))
    (hdual1 : Tendsto (fun n => max
      ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1) /\
    Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1) := by
  constructor
  · exact D.dualMeasure_crossingMax_tendsto_one mu
      (fun n => a0 n + xPad0 n) (fun n => b0 n - xPad0 n) c0 d0
      a0 b0 (fun n => c0 n + yPad0 n) (fun n => d0 n - yPad0 n)
      hdual0
  · exact D.dualMeasure_crossingMax_tendsto_one mu
      (fun n => a1 n + xPad1 n) (fun n => b1 n - xPad1 n) c1 d1
      a1 b1 (fun n => c1 n + yPad1 n) (fun n => d1 n - yPad1 n)
      hdual1


theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hxPad0 : forall n, 4 * B <= xPad0 n)
    (hyPad0 : forall n, 4 * B <= yPad0 n)
    (hxPad1 : forall n, 4 * B <= xPad1 n)
    (hyPad1 : forall n, 4 * B <= yPad1 n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hverticalStart : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      atTop (nhds 1))
    (hhorizontalEnd : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
      atTop (nhds 1))
    (hnormalAdjacent : Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
      atTop (nhds 1))
    (hrotatedDual0 : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
      atTop (nhds 1))
    (hrotatedDual1 : Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
      atTop (nhds 1)) : False := by
  exact PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false
    D mu {
      Bpos := hBpos
      primalArcBound := hBp
      dualArcBound := hBd
      a0 := a0
      b0 := b0
      c0 := c0
      d0 := d0
      a1 := a1
      b1 := b1
      c1 := c1
      d1 := d1
      xPad0 := xPad0
      yPad0 := yPad0
      xPad1 := xPad1
      yPad1 := yPad1
      xPad0_ge := hxPad0
      yPad0_ge := hyPad0
      xPad1_ge := hxPad1
      yPad1_ge := hyPad1
      spanX0 := hspanX0
      spanY0 := hspanY0
      spanX1 := hspanX1
      spanY1 := hspanY1
      verticalStart := hverticalStart
      horizontalEnd := hhorizontalEnd
      primalAdjacent := hnormalAdjacent
      dualLevel0 := hrotatedDual0
      dualLevel1 := hrotatedDual1 }


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_variablePad_normal_rotated_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
    (hxPad0 : forall n, 4 * B <= xPad0 n)
    (hyPad0 : forall n, 4 * B <= yPad0 n)
    (hxPad1 : forall n, 4 * B <= xPad1 n)
    (hyPad1 : forall n, 4 * B <= yPad1 n)
    (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
    (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
    (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
    (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
    (hverticalStart :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
        atTop (nhds 1))
    (hhorizontalEnd :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))
        atTop (nhds 1))
    (hnormalAdjacent :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))))
        atTop (nhds 1))
    (hrotatedDual0 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))))
        atTop (nhds 1))
    (hrotatedDual1 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hverticalStart hhorizontalEnd hnormalAdjacent
  dsimp only at hrotatedDual0 hrotatedDual1
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_normal_rotated_limits _ B hBpos
    hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1
    hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1
    hverticalStart hhorizontalEnd hnormalAdjacent hrotatedDual0 hrotatedDual1


theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d xPad yPad : Nat -> Nat -> Real)
    (hxPad : forall k n, 4 * B <= xPad k n)
    (hyPad : forall k n, 4 * B <= yPad k n)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hvertical : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
      atTop (nhds 1))
    (hhorizontal : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + yPad (k + 1) n)
        (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
    (hnormal : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a (k + 1) n + xPad (k + 1) n)
        (b (k + 1) n - xPad (k + 1) n)
        (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdual : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))))
      atTop (nhds 1)) : False := by
  let f0 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))
  let f1 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a (k + 1) n) (b (k + 1) n)
      (c (k + 1) n + yPad (k + 1) n)
      (d (k + 1) n - yPad (k + 1) n))
  let f2 : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a (k + 1) n + xPad (k + 1) n)
      (b (k + 1) n - xPad (k + 1) n)
      (c (k + 1) n) (d (k + 1) n)))
  let f3 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
  let f4 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a (k + 1) n + xPad (k + 1) n)
        (b (k + 1) n - xPad (k + 1) n)
        (c (k + 1) n) (d (k + 1) n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a (k + 1) n) (b (k + 1) n)
        (c (k + 1) n + yPad (k + 1) n)
        (d (k + 1) n - yPad (k + 1) n)))
  have hf0 (k : Nat) : Tendsto (f0 k) atTop (nhds 1) := by
    simpa only [f0] using hvertical k
  have hf1 (k : Nat) : Tendsto (f1 k) atTop (nhds 1) := by
    simpa only [f1] using hhorizontal k
  have hf2 (k : Nat) : Tendsto (f2 k) atTop (nhds 1) := by
    simpa only [f2] using hnormal k
  have hf3 (k : Nat) : Tendsto (f3 k) atTop (nhds 1) := by
    simpa only [f3] using hdual k
  have hf4 (k : Nat) : Tendsto (f4 k) atTop (nhds 1) := by
    simpa only [f4] using hdual (k + 1)
  obtain ⟨index, _hindex, hall⟩ :=
    exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
      f0 f1 f2 f3 f4 hf0 hf1 hf2 hf3 hf4
      (fun _ _ => measureReal_le_one)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
  let level : Nat -> Nat := fun n => n
  have hlevel (n : Nat) : level n < n + 1 := Nat.lt_succ_self n
  obtain ⟨hv, hh, hn, hd0, hd1⟩ := hall level hlevel
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd
    (fun n => a (level n) (index n))
    (fun n => b (level n) (index n))
    (fun n => c (level n) (index n))
    (fun n => d (level n) (index n))
    (fun n => a (level n + 1) (index n))
    (fun n => b (level n + 1) (index n))
    (fun n => c (level n + 1) (index n))
    (fun n => d (level n + 1) (index n))
    (fun n => xPad (level n) (index n))
    (fun n => yPad (level n) (index n))
    (fun n => xPad (level n + 1) (index n))
    (fun n => yPad (level n + 1) (index n))
    (fun n => hxPad (level n) (index n))
    (fun n => hyPad (level n) (index n))
    (fun n => hxPad (level n + 1) (index n))
    (fun n => hyPad (level n + 1) (index n))
    (fun n => hspanX (level n) (index n))
    (fun n => hspanY (level n) (index n))
    (fun n => hspanX (level n + 1) (index n))
    (fun n => hspanY (level n + 1) (index n))
  · simpa only [f0] using hv
  · simpa only [f1] using hh
  · simpa only [f2] using hn
  · simpa only [f3] using hd0
  · simpa only [f4] using hd1


theorem PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_transitions
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
    (hxPad0 : forall k n, 4 * B <= xPad0 k n)
    (hyPad0 : forall k n, 4 * B <= yPad0 k n)
    (hxPad1 : forall k n, 4 * B <= xPad1 k n)
    (hyPad1 : forall k n, 4 * B <= yPad1 k n)
    (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
    (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
    (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
    (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
    (hvertical : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
        (c0 k n) (d0 k n))) atTop (nhds 1))
    (hhorizontal : forall k, Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a1 k n) (b1 k n)
        (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
      atTop (nhds 1))
    (hnormal : forall k, Tendsto (fun n => max
      (mu.real (D.primalEmbedding.horizontalCrossingEvent
        (a0 k n) (b0 k n)
        (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
      (mu.real (D.primalEmbedding.verticalCrossingEvent
        (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
        (c1 k n) (d1 k n)))) atTop (nhds 1))
    (hdual0 : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
          (c0 k n) (d0 k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a0 k n) (b0 k n)
          (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))))
      atTop (nhds 1))
    (hdual1 : forall k, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
          (c1 k n) (d1 k n)))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a1 k n) (b1 k n)
          (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))))
      atTop (nhds 1)) : False := by
  let f0 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))
  let f1 : Nat -> Nat -> Real := fun k n => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a1 k n) (b1 k n)
      (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))
  let f2 : Nat -> Nat -> Real := fun k n => max
    (mu.real (D.primalEmbedding.horizontalCrossingEvent
      (a0 k n) (b0 k n)
      (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
    (mu.real (D.primalEmbedding.verticalCrossingEvent
      (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))
  let f3 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a0 k n) (b0 k n)
        (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
  let f4 : Nat -> Nat -> Real := fun k n => max
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))
    (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a1 k n) (b1 k n)
        (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
  obtain ⟨index, _hindex, hall⟩ :=
    exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal
      f0 f1 f2 f3 f4
      (fun k => by simpa only [f0] using hvertical k)
      (fun k => by simpa only [f1] using hhorizontal k)
      (fun k => by simpa only [f2] using hnormal k)
      (fun k => by simpa only [f3] using hdual0 k)
      (fun k => by simpa only [f4] using hdual1 k)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
      (fun _ _ => max_le measureReal_le_one measureReal_le_one)
  let level : Nat -> Nat := fun n => n
  have hlevel (n : Nat) : level n < n + 1 := Nat.lt_succ_self n
  obtain ⟨hv, hh, hn, hd0, hd1⟩ := hall level hlevel
  apply D.variablePadTwoLevel_false_of_normal_rotated_limits mu B hBpos
    hBp hBd
    (fun n => a0 (level n) (index n))
    (fun n => b0 (level n) (index n))
    (fun n => c0 (level n) (index n))
    (fun n => d0 (level n) (index n))
    (fun n => a1 (level n) (index n))
    (fun n => b1 (level n) (index n))
    (fun n => c1 (level n) (index n))
    (fun n => d1 (level n) (index n))
    (fun n => xPad0 (level n) (index n))
    (fun n => yPad0 (level n) (index n))
    (fun n => xPad1 (level n) (index n))
    (fun n => yPad1 (level n) (index n))
    (fun n => hxPad0 (level n) (index n))
    (fun n => hyPad0 (level n) (index n))
    (fun n => hxPad1 (level n) (index n))
    (fun n => hyPad1 (level n) (index n))
    (fun n => hspanX0 (level n) (index n))
    (fun n => hspanY0 (level n) (index n))
    (fun n => hspanX1 (level n) (index n))
    (fun n => hspanY1 (level n) (index n))
  · simpa only [f0] using hv
  · simpa only [f1] using hh
  · simpa only [f2] using hn
  · simpa only [f3] using hd0
  · simpa only [f4] using hd1


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_transitions
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
    (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
    (hxPad0 : forall k n, 4 * B <= xPad0 k n)
    (hyPad0 : forall k n, 4 * B <= yPad0 k n)
    (hxPad1 : forall k n, 4 * B <= xPad1 k n)
    (hyPad1 : forall k n, 4 * B <= yPad1 k n)
    (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
    (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
    (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
    (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
    (hvertical :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
          (c0 k n) (d0 k n))) atTop (nhds 1))
    (hhorizontal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a1 k n) (b1 k n)
          (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))
        atTop (nhds 1))
    (hnormal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a0 k n) (b0 k n)
          (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
          (c1 k n) (d1 k n)))) atTop (nhds 1))
    (hdual0 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a0 k n + xPad0 k n) (b0 k n - xPad0 k n)
            (c0 k n) (d0 k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a0 k n) (b0 k n)
            (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))))
        atTop (nhds 1))
    (hdual1 :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a1 k n + xPad1 k n) (b1 k n - xPad1 k n)
            (c1 k n) (d1 k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a1 k n) (b1 k n)
            (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hvertical hhorizontal hnormal hdual0 hdual1
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_pointwise_transitions _ B hBpos
    hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1
    hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1
    hvertical hhorizontal hnormal hdual0 hdual1


theorem PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_variablePad_limits
    (D : PeriodicPlanarDualPair P Pdual)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (B : Real) (hBpos : 0 < B)
    (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
    (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
    (a b c d xPad yPad : Nat -> Nat -> Real)
    (hxPad : forall k n, 4 * B <= xPad k n)
    (hyPad : forall k n, 4 * B <= yPad k n)
    (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
    (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
    (hvertical :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.verticalCrossingEvent
          (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
        atTop (nhds 1))
    (hhorizontal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => mu.real
        (D.primalEmbedding.horizontalCrossingEvent
          (a (k + 1) n) (b (k + 1) n)
          (c (k + 1) n + yPad (k + 1) n)
          (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
    (hnormal :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a (k + 1) n + xPad (k + 1) n)
          (b (k + 1) n - xPad (k + 1) n)
          (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
    (hdual :
      let mu : Measure (ConfigSpace (Sym2 V)) :=
        P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
      forall k, Tendsto (fun n => max
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.verticalCrossingEvent
            (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n)))
        (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.horizontalCrossingEvent
            (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))))
        atTop (nhds 1)) :
    let mu : Measure (ConfigSpace (Sym2 V)) :=
      P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq)
    mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
  dsimp only at hvertical hhorizontal hnormal hdual
  dsimp only
  intro _hcommon
  exact D.variablePadTwoLevel_false_of_pointwise_limits _ B hBpos hBp hBd
    a b c d xPad yPad hxPad hyPad hspanX hspanY
    hvertical hhorizontal hnormal hdual


end StatMech.FK.PeriodicPlanar
