/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part13


namespace StatMech.Universality

open HexWalk


noncomputable def hlha_augmentedTwoHalfData (a : ℂ) (h0 : ℤ) (N : ℕ) :
    HLHRAugmentedTwoHalfData a h0 N where
  lowerBoundary := fun _ => -1
  upperBoundary := fun _ => -1
  lowerCore := fun d => (hlha_prefixAugment d.1).tail
  upperCore := fun d => (hlha_suffixAugment d.1).tail
  decode := hlha_decodeAugmented a h0
  decode_source := by
    intro d
    have hsource := (hhc_Dn_spec a h0 N d).1
    simp only [hlha_decodeAugmented]
    rw [hlha_prefixAugment_cons_tail, hlha_suffixAugment_cons_tail]
    exact hlha_decodePair_augmented a h0 d.1 hsource
  core_length := by
    intro d
    exact hlha_augmentedCore_length a h0 d.1 (hhc_Dn_spec a h0 N d).1
  lower_legal := by
    intro d
    rw [hlha_prefixAugment_cons_tail]
    exact (hlha_prefixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).1
  upper_legal := by
    intro d
    rw [hlha_suffixAugment_cons_tail]
    exact (hlha_suffixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).1
  lower_halfSpace := by
    intro d
    rw [hlha_prefixAugment_cons_tail]
    exact (hlha_prefixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).2.1
  upper_halfSpace := by
    intro d
    rw [hlha_suffixAugment_cons_tail]
    exact (hlha_suffixAugment_spec a h0 d.1 (hhc_Dn_spec a h0 N d).1).2.1


end StatMech.Universality
