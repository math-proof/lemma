/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectEndpoint
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
open MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Sharpness StatMech.FrontierB

noncomputable section

def ons_originPositiveBoxVertex (n : Nat) : sctBox 2 (n + 1) :=
  ⟨![0, 0], by
    intro i
    fin_cases i <;> simp⟩


def ons_neighborPositiveBoxVertex (n : Nat) : sctBox 2 (n + 1) :=
  ⟨![1, 0], by
    intro i
    fin_cases i <;> simp⟩

end
end StatMech.Onsager
