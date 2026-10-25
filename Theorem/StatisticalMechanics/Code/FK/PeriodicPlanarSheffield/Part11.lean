/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffield.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCoverage.Part3
import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part11
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


@[simp] theorem PeriodicGraph.shift_neg_shift
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.shift (-z) (P.shift z x) = x := by
  have h := P.shift_add z (-z) x
  rw [add_neg_cancel, P.shift_zero] at h
  exact h.symm

@[simp] theorem PeriodicGraph.shift_shift_neg
    (P : PeriodicGraph V) (z : Site 2) (x : V) :
    P.shift z (P.shift (-z) x) = x := by
  simpa only [neg_neg] using P.shift_neg_shift (-z) x

@[simp] theorem PeriodicGraph.configTranslate_neg
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) :
    P.configTranslate (-z) (P.configTranslate z omega) = omega := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [PeriodicGraph.configTranslate]

theorem PeriodicGraph.measurable_configTranslate
    (P : PeriodicGraph V) (z : Site 2) :
    Measurable (P.configTranslate z) :=
  measurable_pi_lambda _ fun e => ConfigSpace.measurable_eval _


end StatMech.FK.PeriodicPlanar
