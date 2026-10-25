/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCutGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Structure.StatisticalMechanics.Code.Universality.HexCorrectedHighestCutGeometry.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexCSHighestCutGeometry

variable {T : ℕ} {hT : 1 ≤ T}


noncomputable def toHighestCut
    (G : HexCSHighestCutGeometry T hT) : HexCSHighestCut T hT where
  split := fun d =>
    (⟨(G.cut d).outputPair.1, (G.cut d).prefix_top⟩,
      ⟨(G.cut d).outputPair.2, (G.cut d).suffix_top⟩)
  split_injective := by
    intro d e hde
    apply Subtype.ext
    have hpairs : (G.cut d).outputPair = (G.cut e).outputPair := by
      exact Prod.ext
        (congrArg (fun p => p.1.1) hde)
        (congrArg (fun p => p.2.1) hde)
    calc
      d.1 = hexCSDecodeCutPair (G.cut d).outputPair :=
        (G.cut d).decode_outputPair.symm
      _ = hexCSDecodeCutPair (G.cut e).outputPair := congrArg _ hpairs
      _ = e.1 := (G.cut e).decode_outputPair
  length_add_one := by
    intro d
    change (G.cut d).outputPair.1.length +
        (G.cut d).outputPair.2.length = d.1.length + 1
    exact (G.cut d).output_length_add_one

end HexCSHighestCutGeometry


noncomputable def hexCS_highestCuts_of_geometry
    (G : ∀ T (hT : 1 ≤ T), HexCSHighestCutGeometry T hT) :
    ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT :=
  fun T hT => (G T hT).toHighestCut

end
end StatMech.Universality
