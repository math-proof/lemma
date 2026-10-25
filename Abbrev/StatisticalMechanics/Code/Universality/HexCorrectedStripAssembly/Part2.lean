/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part7


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

abbrev HexCSPairIndex (T L : ℕ) :=
  {e : HexCSIncidence T L //
    e ∈ hexCSBoundaryIncidences T L ∧
      hexCSIncidenceRank e < hexCSIncidenceRank (hexCSReflectIncidence e)}

abbrev HexCSFixedIndex (T L : ℕ) (hT : 0 < T) :=
  {e : HexCSIncidence T L //
    e ∈ hexCSBoundaryIncidences T L ∧
      hexCSReflectIncidence e = e ∧
      e ≠ hexCSStartIncidence T L hT}

end
end StatMech.Universality
