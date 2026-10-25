/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


section Wired

variable (bdry : V → Prop) [DecidablePred bdry]


@[simp] theorem cfe_wiredCentered_zero (q : ℝ) : cfe_wiredCentered G bdry q 0 = 0 := by
  unfold cfe_wiredCentered; ring


theorem cfe_wiredCentered_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (cfe_wiredCentered G bdry q) := by
  have hconv : ConvexOn ℝ univ (wpd_wiredTiltFreeEnergy G bdry q) :=
    wpd_wiredTiltFreeEnergy_convexOn G bdry q hq hE
  have heq : cfe_wiredCentered G bdry q
      = (fun t => wpd_wiredTiltFreeEnergy G bdry q t + (- wpd_wiredTiltFreeEnergy G bdry q 0)) := by
    funext t; unfold cfe_wiredCentered; ring
  rw [heq]; exact hconv.add_const _


theorem cfe_wiredCentered_hasDerivAt (hE : 0 < G.edgeFinset.card) (t : ℝ) :
    HasDerivAt (cfe_wiredCentered G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
  have hbase : HasDerivAt (wpd_wiredTiltFreeEnergy G bdry 2) (wpd_avgWiredDensity G bdry 2 t) t := by
    have h := wpd_wiredTiltFreeEnergy_hasDerivAt G bdry 2 (by norm_num) hE t
    rwa [show (1 / (G.edgeFinset.card : ℝ))
        * wpd_wiredFkExpect G bdry (fsc_logistic t) 2 (fun ω => (openCount G ω : ℝ))
        = wpd_avgWiredDensity G bdry 2 t from rfl] at h
  exact hbase.sub_const (wpd_wiredTiltFreeEnergy G bdry 2 0)

end Wired
end FK
end StatMech
