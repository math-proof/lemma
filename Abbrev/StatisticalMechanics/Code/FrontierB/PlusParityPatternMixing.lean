/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
import Def.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

abbrev PlusParityExpansionIndex (d : Nat) :=
  Sigma fun _ : Finset (Sym2 (Site d)) =>
    Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)

end StatMech.FrontierB
