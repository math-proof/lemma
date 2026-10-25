/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part14
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem pairedEdgeCutIntersection_iff_twoColorHexAlternative
    {V I : Type*} (source target : I → Sym2 V) (R L : Set V) :
    PairedEdgeCutIntersection source target R L ↔
      PairedEdgeTwoColorHexAlternative source target R L := by
  classical
  constructor
  · intro hintersect A B hRA hLA hRB hLB hmono
    obtain ⟨i, hsource, htarget⟩ :=
      hintersect A B hRA hLA hRB hLB
    rcases hmono i with hsourceMono | htargetMono
    · exact
        (rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
          A (source i)).mpr hsourceMono hsource
    · exact
        (rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
          B (target i)).mpr htargetMono htarget
  · intro hhex A B hRA hLA hRB hLB
    by_contra hintersect
    apply hhex A B hRA hLA hRB hLB
    intro i
    have hi : ¬(rlc_twoChannelFullPhysicalEdgeCrossesCut A (source i) ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B (target i)) := by
      intro hboth
      exact hintersect ⟨i, hboth⟩
    rcases not_and_or.mp hi with hsource | htarget
    · exact Or.inl
        ((rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
          A (source i)).mp hsource)
    · exact Or.inr
        ((rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
          B (target i)).mp htarget)


end
end StatMech.Universality
