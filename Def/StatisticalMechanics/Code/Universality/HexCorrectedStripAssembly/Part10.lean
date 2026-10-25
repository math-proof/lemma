/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part8


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

def hexCSHeading {T L : ℕ} (v : HexCSVertex T L) (e : Fin 3) : ℤ :=
  hexCSCanonicalHeading ⟨v, e⟩

end
end StatMech.Universality
