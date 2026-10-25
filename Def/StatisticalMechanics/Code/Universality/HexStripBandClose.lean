/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripBandClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexStripWindingClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


noncomputable def hexJordan_vertexPos (a : ℂ) (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℂ :=
  hexInfra_midAccum a h0 (ts.take k) + halfStep (hexInfra_headAccum h0 (ts.take k))


end StatMech.Universality
