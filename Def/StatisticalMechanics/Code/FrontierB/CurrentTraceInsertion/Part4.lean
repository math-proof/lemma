/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
import Theorem.StatisticalMechanics.Code.FK.InfiniteFiniteEnergy.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceInsertion.Part3
open MeasureTheory
open scoped ENNReal BigOperators symmDiff


namespace StatMech.FrontierB

open Sharpness Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def HasLatticeFiniteEnergyMerge
    {d : ℕ} (mu : Measure (ConfigSpace (Sym2 (Site d)))) : Prop :=
  ∀ F : Finset (Sym2 (Site d)),
    (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet →
      mu.map (fun omega => StatMech.Percolation.forceOpenFinset F omega) ≪ mu


end StatMech.FrontierB
