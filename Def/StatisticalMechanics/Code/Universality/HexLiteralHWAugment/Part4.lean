module
public import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk


noncomputable def hlha_realizeCoord (m s : ℂ) (h : ℤ)
    (p r : HexReturnCoord) : ℂ :=
  m + halfStep h + 2 * ((r.value - p.value) * s)


end StatMech.Universality
