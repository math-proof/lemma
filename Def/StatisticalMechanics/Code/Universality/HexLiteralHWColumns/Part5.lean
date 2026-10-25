/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def HLHCMidpointColumnWalk.stripHeight
    {T : ℕ} {ts : List ℤ} (W : HLHCMidpointColumnWalk T ts) : ℕ :=
  max (Finset.univ.sup (fun k : Fin ts.length =>
      hlhc_coordBound (W.midCoord k)))
    (hlhc_coordBound W.topCoord)

end
end StatMech.Universality
