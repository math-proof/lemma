/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhda_score (p : HexReturnCoord) : ℤ := 2 * p.x - p.y

def hlhda_spacerWhite : HexReturnCoord := ⟨0, -1⟩

def hlhda_spacerRoot : HexReturnCoord := ⟨1, -1⟩

def hlhda_flatNeighbor : HexReturnCoord := ⟨-1, 0⟩

end
end StatMech.Universality
