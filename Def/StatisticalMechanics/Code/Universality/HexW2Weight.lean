/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Weight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Structure.StatisticalMechanics.Code.Universality.HexW2Weight


namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hexW2_halfWt (x : ℝ) (b : HexW2Half) : ℝ :=
  hexSAWwt b.mid b.head x b.turns


end StatMech.Universality
