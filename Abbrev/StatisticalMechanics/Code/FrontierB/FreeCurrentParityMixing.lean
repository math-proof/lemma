/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeCurrentParityMixing
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

abbrev FreeParityExpansionIndex (d : Nat) :=
  Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Sym2 (Site d))

end StatMech.FrontierB
