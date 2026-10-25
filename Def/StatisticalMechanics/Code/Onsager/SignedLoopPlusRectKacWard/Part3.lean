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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectKacWard.Part2
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusRectKWDet (n : Nat) (q : Real) : Complex :=
  (1 - kwGraphTransition
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (fun _ => (q : Complex))
    (ons_rectDualStraightLineEmbedding
      (2 * n + 1) (2 * n + 1)).turnPhase).det


def ons_plusRectPathKWDet (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real) : Complex :=
  (1 - kwGraphTransition
    (ons_rectDualGraph (2 * n + 1) (2 * n + 1))
    (ons_plusRectPathWeight n path q)
    (ons_rectDualStraightLineEmbedding
      (2 * n + 1) (2 * n + 1)).turnPhase).det


end
end StatMech.Onsager
