/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part12


namespace StatMech.Universality

open HexWalk


noncomputable def hlha_decodeAugmented (a : ℂ) (h0 : ℤ)
    (lowerBoundary : ℤ) (lowerCore : List ℤ)
    (upperBoundary : ℤ) (upperCore : List ℤ) : List ℤ :=
  hlha_decodePair a h0
    (lowerBoundary :: lowerCore, upperBoundary :: upperCore)


end StatMech.Universality
