/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part2


namespace StatMech.Universality

open HexWalk

noncomputable def hexEndpointSAWCountR (a : ℂ) (h0 : ℤ) (n : ℕ) : ℝ :=
  (hexEndpointSAWCount a h0 n : ℝ)


noncomputable def hexEndpointCoeffWeight
    (a : ℂ) (h0 : ℤ) (x : ℝ) (n : ℕ) : ℝ :=
  hexEndpointSAWCountR a h0 n * x ^ n

end StatMech.Universality
