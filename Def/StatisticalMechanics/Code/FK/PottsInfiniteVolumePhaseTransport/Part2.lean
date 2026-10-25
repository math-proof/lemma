/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Mathlib.MeasureTheory.Measure.Portmanteau
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolumePhaseTransport
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

noncomputable def pottsColorProbWired
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (bdry : V -> Prop) [DecidablePred bdry]
    (q : Nat) (b a : Fin q) (beta J : Real) (x : V) : Real :=
  ∑ sigma : V -> Fin q, pottsProbWired G bdry q b beta J sigma *
    (if sigma x = a then 1 else 0)

end
end StatMech.FK
