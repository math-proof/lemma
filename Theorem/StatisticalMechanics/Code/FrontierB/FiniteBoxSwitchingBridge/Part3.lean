/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoxSwitchingBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentConnectivityDiagonal.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoxSwitchingBridge.Part3
open MeasureTheory Set SimpleGraph
open scoped ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice Percolation


theorem sourcePairSuperpositionEvent_finiteBoxTracePredicate
    (d n : ℕ) (Q : Set (ConfigSpace (Sym2 (Site d)))) :
    sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n)
        (finiteBoxTracePredicate d n Q) =
      (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹'
        (superposedCurrentTrace ⁻¹' Q) := by
  ext pq
  change finiteBoxCurrentTrace d n
      (ofEdgeFun (StatMech.FK.boxGraph d n)
        (fun e => pq.1 e + pq.2 e)) ∈ Q ↔
    superposedCurrentTrace
      (extendBoxCurrent d n pq.1, extendBoxCurrent d n pq.2) ∈ Q
  rw [finiteBoxCurrentTrace_ofEdgeFun_add]


theorem sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected
    (d n : ℕ) (Q : Set (ConfigSpace (Sym2 (Site d))))
    (x y : StatMech.FK.boxVerts d n) :
    sourcePairSuperpositionEvent (StatMech.FK.boxGraph d n)
        (fun m => finiteBoxTracePredicate d n Q m ∧
          CurrentConnected (StatMech.FK.boxGraph d n) m x y) =
      (Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹'
        currentPairTraceBoxGate Q n (x : Site d) (y : Site d) := by
  ext pq
  change (finiteBoxCurrentTrace d n
      (ofEdgeFun (StatMech.FK.boxGraph d n)
        (fun e => pq.1 e + pq.2 e)) ∈ Q ∧
      CurrentConnected (StatMech.FK.boxGraph d n)
        (ofEdgeFun (StatMech.FK.boxGraph d n)
          (fun e => pq.1 e + pq.2 e)) x y) ↔ _
  rw [finiteBoxCurrentTrace_ofEdgeFun_add,
    currentConnected_ofEdgeFun_add_iff_boxConnectionEvent]
  rfl


theorem freeBoxCurrentMeasure_prod_apply
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : Set (InfiniteCurrentConfig (Sym2 (Site d)) ×
      InfiniteCurrentConfig (Sym2 (Site d)))) (hC : MeasurableSet C) :
    ((freeBoxCurrentMeasure d n beta hbeta).prod
        (freeBoxCurrentMeasure d n beta hbeta) : Measure _) C =
      (sourceCurrentPairPMF (StatMech.FK.boxGraph d n) beta (fun _ => 1)
        hbeta (fun _ => by positivity) ∅ ∅
        (Ising.acr_currentSum_empty_pos
          (StatMech.FK.boxGraph d n) beta (fun _ => 1))
        (Ising.acr_currentSum_empty_pos
          (StatMech.FK.boxGraph d n) beta (fun _ => 1))).toMeasure
          ((Prod.map (extendBoxCurrent d n) (extendBoxCurrent d n)) ⁻¹' C) := by
  let G := StatMech.FK.boxGraph d n
  let mu := (sourcelessCurrentPMF G beta (fun _ => 1) hbeta
    (fun _ => by positivity)).toMeasure
  change (Measure.map (extendBoxCurrent d n) mu).prod
      (Measure.map (extendBoxCurrent d n) mu) C = _
  rw [Measure.map_prod_map mu mu (measurable_extendBoxCurrent d n)
    (measurable_extendBoxCurrent d n),
    Measure.map_apply
      ((measurable_extendBoxCurrent d n).prodMap
        (measurable_extendBoxCurrent d n)) hC,
    sourceCurrentPairPMF_toMeasure_eq_prod]
  rfl


theorem pairSource_free_box_switching
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ENNReal.ofReal
        (currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} *
          currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y}) *
      ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _)
          (superposedCurrentTrace ⁻¹' Q) =
    ENNReal.ofReal
        (currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅ *
          currentSum (StatMech.FK.boxGraph d n) beta (fun _ => 1) ∅) *
      ((freeBoxCurrentMeasure d n beta hbeta.le).prod
        (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _)
          (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
  let G := StatMech.FK.boxGraph d n
  let P : Current (StatMech.FK.boxVerts d n) → Prop :=
    finiteBoxTracePredicate d n Q
  letI : DecidablePred P := Classical.decPred _
  have hpair := boxCurrentSum_pair_pos d n beta hbeta x y hxy
  have hemptyDelta :
      ((∅ : Finset (StatMech.FK.boxVerts d n)) ∆ {x, y}) = {x, y} := by
    ext z
    simp [Finset.mem_symmDiff]
  have hpairDelta : 0 < currentSum G beta (fun _ => 1)
      ((∅ : Finset (StatMech.FK.boxVerts d n)) ∆ {x, y}) := by
    rw [hemptyDelta]
    exact hpair
  have hzero := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hswitch := sourceCurrentPairPMF_switching G beta (fun _ => 1)
    hbeta.le (fun _ => by positivity) (∅ : Finset (StatMech.FK.boxVerts d n))
    hxy P hpairDelta hpair hzero hzero
  rw [sourcePairSuperpositionEvent_finiteBoxTracePredicate d n Q,
    sourcePairSuperpositionEvent_finiteBoxTracePredicate_connected d n Q x y]
    at hswitch
  simp only [hemptyDelta] at hswitch
  have htrace : MeasurableSet (superposedCurrentTrace ⁻¹' Q) :=
    hQ.isOpen.measurableSet.preimage continuous_superposedCurrentTrace.measurable
  have hgate : MeasurableSet
      (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) :=
    (isClopen_currentPairTraceBoxGate hQ n (x : Site d) (y : Site d)).isOpen.measurableSet
  rw [← pairSourceBoxCurrentMeasure_prod_apply
      d n beta hbeta x y hxy (superposedCurrentTrace ⁻¹' Q) htrace,
    ← freeBoxCurrentMeasure_prod_apply d n beta hbeta.le
      (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) hgate]
    at hswitch
  simpa only [G] using hswitch


theorem pairSource_free_box_switching_normalized
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    ENNReal.ofReal
        (expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} ^ 2) *
      ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _)
          (superposedCurrentTrace ⁻¹' Q) =
      ((freeBoxCurrentMeasure d n beta hbeta.le).prod
        (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _)
          (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
  let G := StatMech.FK.boxGraph d n
  let a := currentSum G beta (fun _ => 1) {x, y}
  let z := currentSum G beta (fun _ => 1) ∅
  let p := ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
    (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _)
      (superposedCurrentTrace ⁻¹' Q)
  let q := ((freeBoxCurrentMeasure d n beta hbeta.le).prod
    (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _)
      (currentPairTraceBoxGate Q n (x : Site d) (y : Site d))
  have ha : 0 < a := boxCurrentSum_pair_pos d n beta hbeta x y hxy
  have hz : 0 < z := Ising.acr_currentSum_empty_pos G beta (fun _ => 1)
  have hswitch : ENNReal.ofReal (a * a) * p = ENNReal.ofReal (z * z) * q := by
    simpa only [G, a, z, p, q] using
      pairSource_free_box_switching d n beta hbeta x y hxy Q hQ
  have hcorr : expectationJ G beta (fun _ => 1) {x, y} = a / z := by
    simpa only [a, z] using current_representation G beta (fun _ => 1) {x, y}
  let A := ENNReal.ofReal a
  let Z := ENNReal.ofReal z
  have hZ0 : Z ≠ 0 := (ENNReal.ofReal_pos.mpr hz).ne'
  have hZtop : Z ≠ ∞ := ENNReal.ofReal_ne_top
  have hZZ0 : Z * Z ≠ 0 := mul_ne_zero hZ0 hZ0
  have hZZtop : Z * Z ≠ ∞ := ENNReal.mul_ne_top hZtop hZtop
  apply (ENNReal.mul_left_inj hZZ0 hZZtop).mp
  rw [hcorr, pow_two, ENNReal.ofReal_mul (div_nonneg ha.le hz.le),
    ENNReal.ofReal_div_of_pos hz]
  rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_mul hz.le] at hswitch
  change ((A / Z) * (A / Z) * p) * (Z * Z) = q * (Z * Z)
  calc
    ((A / Z) * (A / Z) * p) * (Z * Z) = A * A * p := by
      rw [div_eq_mul_inv]
      calc
        ((A * Z⁻¹) * (A * Z⁻¹) * p) * (Z * Z) =
            A * A * p * (Z⁻¹ * Z) * (Z⁻¹ * Z) := by ac_rfl
        _ = A * A * p := by rw [ENNReal.inv_mul_cancel hZ0 hZtop]; simp
    _ = Z * Z * q := by simpa only [A, Z] using hswitch
    _ = q * (Z * Z) := by ac_rfl


theorem pairSource_free_box_switching_normalized_real
    (d n : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (x y : StatMech.FK.boxVerts d n) (hxy : x ≠ y)
    (Q : Set (ConfigSpace (Sym2 (Site d)))) (hQ : IsClopen Q) :
    expectationJ (StatMech.FK.boxGraph d n) beta (fun _ => 1) {x, y} ^ 2 *
      ((pairSourceBoxCurrentMeasure d n beta hbeta x y hxy).prod
        (pairSourceBoxCurrentMeasure d n beta hbeta x y hxy) : Measure _).real
          (superposedCurrentTrace ⁻¹' Q) =
      ((freeBoxCurrentMeasure d n beta hbeta.le).prod
        (freeBoxCurrentMeasure d n beta hbeta.le) : Measure _).real
          (currentPairTraceBoxGate Q n (x : Site d) (y : Site d)) := by
  have h := congrArg ENNReal.toReal
    (pairSource_free_box_switching_normalized
      d n beta hbeta x y hxy Q hQ)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    Measure.real] using h

end StatMech.FrontierB
