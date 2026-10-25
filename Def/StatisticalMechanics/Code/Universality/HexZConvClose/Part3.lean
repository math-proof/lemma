/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part2


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


noncomputable def hzc_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) : ℕ :=
  ((hzc_truncFinset a h0 (n + 1)).filter
    (fun ts => (ofTurns a h0 ts).numVertices = n)).card


end StatMech.Universality
