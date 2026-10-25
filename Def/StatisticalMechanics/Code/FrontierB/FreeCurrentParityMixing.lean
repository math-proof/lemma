/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeCurrentParityMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.PlusParityPatternMixing.Part2
import Abbrev.StatisticalMechanics.Code.FrontierB.FreeCurrentParityMixing
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

noncomputable def freeParityExpansionIndices {d : Nat}
    (S : Finset (Sym2 (Site d))) : Finset (FreeParityExpansionIndex d) :=
  S.powerset.sigma fun T => T.powerset

noncomputable def freeParityExpansionCoeff {d : Nat} (beta : Real)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (i : FreeParityExpansionIndex d) : Real :=
  currentParityTraceCoeff S odd i.1 * Real.cosh beta ^ i.1.card *
    edgeExpansionCoeff beta i.1 i.2

noncomputable def freeParityExpansionSupport {d : Nat}
    (i : FreeParityExpansionIndex d) : Finset (Site d) :=
  edgeBoundary (i.1 \ i.2)

end StatMech.FrontierB
