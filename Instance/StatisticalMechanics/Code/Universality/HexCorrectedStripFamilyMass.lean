/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable instance hexCSClassWalkDecidable
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass)
    (ts : List ℤ) : Decidable (HexCSClassWalk T L hT cls ts) :=
  Classical.propDecidable _

end
end StatMech.Universality
