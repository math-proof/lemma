module
public import Theorem.StatisticalMechanics.Code.FrontierB.GenMixingCofinite
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityReduction.Part2
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhaseTransport.Part3
open MeasureTheory Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPersistence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

open StatMech.OSSS.FKSharpnessWeightedPhaseTransport


noncomputable def originShiftBox (d R : Nat) :
    Finset (Multiplicative (Site d)) :=
  (box_finite d R).toFinset.image
    (fun x => Multiplicative.ofAdd (-x))

end StatMech.FrontierB
