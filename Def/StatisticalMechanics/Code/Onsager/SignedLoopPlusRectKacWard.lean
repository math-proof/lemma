/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part12
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCutLimit
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusRectContourSum (n : Nat) (q : Real) : Real :=
  ∑ F : ons_PlusRectEvenSubgraph n, q ^ F.1.card


def ons_plusRectPathSum (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) : Real :=
  ∑ F : ons_PlusRectEvenSubgraph n,
    ons_plusRectPathDefectSign n path F * q ^ F.1.card

end
end StatMech.Onsager
