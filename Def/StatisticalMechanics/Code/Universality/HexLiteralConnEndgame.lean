/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralConnEndgame.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real


noncomputable def hexLiteralSAWCount (n : ℕ) : ℝ :=
  hlc_sawCountR 0 0 n


end StatMech.Universality
