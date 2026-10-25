/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthSubcritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhds_twoHalfData (N : ℕ) :
    HLHDTaggedTwoHalfData hexAWStart 1 N 4 where
  lower := fun d => hlhda_prefixAugment d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper := fun d => hlhda_suffixAugment d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  lower_legal := fun d => hlhda_prefixAugment_isLegalSAW d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper_legal := fun d => hlhda_suffixAugment_isLegalSAW d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  lower_halfSpace := fun d => hlhda_prefixAugment_halfSpace d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  upper_halfSpace := fun d => hlhda_suffixAugment_halfSpace d.1
    (hhc_Dn_spec hexAWStart 1 N d).1
  pair_injective := by
    intro d e hpair
    apply Subtype.ext
    apply hlhda_augmentedPair_injective
      (hhc_Dn_spec hexAWStart 1 N d).1
      (hhc_Dn_spec hexAWStart 1 N e).1
    simpa only [hlhda_augmentedPair] using hpair
  length_add := by
    intro d
    simpa only [hlhda_augmentedPair] using
      hlhda_augmentedPair_length d.1
        (hhc_Dn_spec hexAWStart 1 N d).1


end
end StatMech.Universality
