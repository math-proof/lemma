module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk


def hls_allTrue : Fin 6 → Bool := fun _ => true


def hls_allFalse : Fin 6 → Bool := fun _ => false


end StatMech.Universality
