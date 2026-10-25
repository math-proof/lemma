/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part12


namespace StatMech.Universality

open HexWalk


@[simp] theorem hlha_decodePair_augmented (a : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hsource : (ofTurns a h0 ts).IsLegalSAW) :
    hlha_decodePair a h0 (hlha_augmentedPair ts) = ts := by
  classical
  unfold hlha_decodePair
  rw [dif_pos ⟨ts, hsource, rfl⟩]
  let h : ∃ us : List ℤ,
      (ofTurns a h0 us).IsLegalSAW ∧
        hlha_augmentedPair us = hlha_augmentedPair ts :=
    ⟨ts, hsource, rfl⟩
  have hchosen := Classical.choose_spec h
  exact hlha_augmentedPair_injective a h0 hchosen.1 hsource hchosen.2


end StatMech.Universality
