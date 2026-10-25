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
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectKacWard
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA

noncomputable section

def ons_plusRectPathWeight (n : Nat) {u v : Site 2}
    (path : (hypercubicLattice 2).Walk u v) (q : Real)
    (edge : Sym2 (ons_RectDualVertex (2 * n + 1) (2 * n + 1))) : Complex :=
  (ons_plusRectPathEdgeSign n path edge : Complex) * (q : Complex)


end
end StatMech.Onsager
