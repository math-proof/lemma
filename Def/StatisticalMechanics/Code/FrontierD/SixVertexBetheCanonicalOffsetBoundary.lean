/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOffsetBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedOffset.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddOffsetBoundaryEstimate


namespace StatMech.FrontierD

open Finset

noncomputable section

def sixVertexCanonicalEvenLeftBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨i, by omega⟩

def sixVertexCanonicalEvenRightBoundaryIndex (s k : Nat) (i : Fin s) :
    Fin ((2 * s + k + 1) + (2 * s + k + 1)) :=
  ⟨s + ((s + k + 1) + (s + k + 1)) + i, by omega⟩

end
end StatMech.FrontierD
