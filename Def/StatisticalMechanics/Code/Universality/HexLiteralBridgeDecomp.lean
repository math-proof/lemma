/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4


namespace StatMech.Universality

open HexWalk


def hexHW_LiteralPositiveWalk (a : ℂ) (h0 : ℤ) (ts : List ℤ) : Prop :=
  (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧
    (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)


noncomputable def hexHW_literalSplit (a : ℂ) (h0 : ℤ) :
    {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts} → HexW2Half × HexW2Half :=
  hexW2_split a h0 (hexHW_LiteralPositiveWalk a h0)


end StatMech.Universality
