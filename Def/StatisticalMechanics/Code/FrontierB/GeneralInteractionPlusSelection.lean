/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionPlusSelection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionPlusParity
import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionPlusSelection
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


def GeneralPlusParityAvoidanceConverges {d : Nat}
    (J : Sym2 (Site d) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (beta : ℝ) (hbeta : 0 < beta) : Prop :=
  ∀ F : Finset (Sym2 (Site d)), ∃ L : ℝ≥0∞, Tendsto
    (fun n ↦ (generalPlusBoxCurrentMeasure J hJ n beta hbeta.le :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        (currentParityAvoidCylinder F)) atTop (nhds L)


end StatMech.FrontierB
