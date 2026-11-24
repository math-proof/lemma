module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralSubcritical


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


def hls_encode (a : ℂ) (h0 : ℤ) (n : ℕ) (d : hls_ExactSAW a h0 n) :
    Fin n → Bool := fun i =>
  decide (d.1.get ⟨i.1, by rw [hls_exact_length a h0 n d]; exact i.2⟩ = 1)


end StatMech.Universality
