/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Def.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part17
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma measurableSet_centerStateEvent (s : Fin 2) :
    MeasurableSet (centerStateEvent s) := by
  have hcoord : Measurable (fun sigma : ConfigSpace (Site 1) => sigma (origin 1)) :=
    measurable_pi_apply _
  have hstate : Measurable (fun b : Bool => boolTransferState b) :=
    measurable_of_finite _
  exact (hstate.comp hcoord) (measurableSet_singleton s)

lemma origin_one_eq_site1_zero : origin 1 = site1 0 := by
  funext i
  fin_cases i
  rfl

lemma fvPathState_center (eta : ConfigSpace (Site 1)) (n : ℕ)
    (tau : {x // x ∈ box 1 n} → Bool) :
    fvPathState eta n tau (n + 1) =
      boolTransferState (glue eta tau (origin 1)) := by
  unfold fvPathState
  rw [origin_one_eq_site1_zero]
  congr 2
  push_cast
  ring_nf


theorem fvMeasure_centerStateEvent_real
    (eta : ConfigSpace (Site 1)) (n : ℕ) (beta h : ℝ) (s : Fin 2) :
    (fvMeasure eta n (bondFinsetTouch 1 n) beta h).real (centerStateEvent s) =
      fvCenterStateProb eta n beta h s := by
  rw [fvMeasure_real_eq eta n (bondFinsetTouch 1 n) beta h
    (measurableSet_centerStateEvent s)]
  unfold fvCenterStateProb
  apply Finset.sum_congr rfl
  intro tau htau
  rw [fvPathState_center]
  by_cases hs : boolTransferState (glue eta tau (origin 1)) = s
  · rw [if_pos hs]
    simp [centerStateEvent, hs]
  · rw [if_neg hs]
    simp [centerStateEvent, hs]


theorem fvMeasure_centerStateEvent_tendsto
    (eta : ℕ → ConfigSpace (Site 1)) (beta h : ℝ) (s : Fin 2) :
    Filter.Tendsto
      (fun n => (fvMeasure (eta n) n (bondFinsetTouch 1 n) beta h).real
        (centerStateEvent s))
      Filter.atTop (nhds (isingTransferProjectorPlus beta (beta * h) s s)) := by
  simpa only [fvMeasure_centerStateEvent_real] using
    fvCenterStateProb_tendsto eta beta h s


end StatMech.FrontierB
