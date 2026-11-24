module
public import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
open Filter MeasureTheory
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising Lattice


def pairSourceBoxSite {d n : ℕ} (x : Site d) (hx : x ∈ box d n) :
    StatMech.FK.boxVerts d n :=
  ⟨x, hx⟩

end StatMech.FrontierB
