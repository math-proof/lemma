/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part3


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

noncomputable def verticesAux (m : ℂ) (h : ℤ) : List ℤ → List ℂ
  | [] => [m + halfStep h]
  | t :: ts => (m + halfStep h) :: verticesAux (m + halfStep h + halfStep (h + t)) (h + t) ts


noncomputable def vertices (w : HexWalk) : List ℂ := verticesAux w.startMid w.h0 w.turns

end HexWalk
end StatMech.Universality
