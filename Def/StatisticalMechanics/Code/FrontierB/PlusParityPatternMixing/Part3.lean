/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusParityPatternMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing.Part2
import Abbrev.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

noncomputable def plusParityExpansionIndices {d : Nat}
    (S : Finset (Sym2 (Site d))) : Finset (PlusParityExpansionIndex d) :=
  S.powerset.sigma fun T => plusEvenExpansionIndices T

noncomputable def plusParityExpansionCoeff {d : Nat} (beta : Real)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (i : PlusParityExpansionIndex d) : Real :=
  currentParityTraceCoeff S odd i.1 * Real.cosh beta ^ i.1.card *
    plusEvenExpansionCoeff beta i.1 i.2

def plusParityExpansionSupport {d : Nat}
    (i : PlusParityExpansionIndex d) : Finset (Site d) := i.2.2


end StatMech.FrontierB
