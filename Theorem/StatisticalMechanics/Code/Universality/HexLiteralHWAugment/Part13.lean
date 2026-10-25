/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part13


namespace StatMech.Universality

open HexWalk


theorem hlha_augmentedCore_length (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    (hlha_prefixAugment ts).tail.length +
        (hlha_suffixAugment ts).tail.length = ts.length := by
  have hp := (hlha_prefixAugment_spec a h0 ts hsource).2.2
  have hs := (hlha_suffixAugment_spec a h0 ts hsource).2.2
  have hpc := congrArg List.length (hlha_prefixAugment_cons_tail ts)
  have hsc := congrArg List.length (hlha_suffixAugment_cons_tail ts)
  have hsplit := congrArg List.length
    (List.take_append_drop (hexW2_cutPos 0 ts) ts)
  simp only [List.length_cons, List.length_append] at hpc hsc hsplit
  omega


end StatMech.Universality
