/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PairMixingCofinite
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.FrontierB.PlusEvenMixing
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

noncomputable def plusEvenExpansionIndices {d : Nat}
    (F : Finset (Sym2 (Site d))) :
    Finset (Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) :=
  F.powerset.sigma fun T => (edgeBoundary (F \ T)).powerset

noncomputable def plusEvenExpansionCoeff {d : Nat} (beta : Real)
    (F : Finset (Sym2 (Site d)))
    (i : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) : Real :=
  edgeExpansionCoeff beta F i.1 *
    plusSpinExpansionCoeff (edgeBoundary (F \ i.1)) i.2

def plusEvenExpansionSupport {d : Nat}
    (i : Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Site d)) :
    Finset (Site d) := i.2

noncomputable def edgeVertexSupport {d : Nat} (F : Finset (Sym2 (Site d))) :
    Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

end StatMech.FrontierB
