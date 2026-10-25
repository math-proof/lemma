/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part11


namespace StatMech.Universality

open HexWalk


noncomputable def hlha_decodePair (a : ℂ) (h0 : ℤ)
    (p : List ℤ × List ℤ) : List ℤ := by
  classical
  exact if h : ∃ ts : List ℤ,
      (ofTurns a h0 ts).IsLegalSAW ∧ hlha_augmentedPair ts = p then
    Classical.choose h
  else []

end StatMech.Universality
