/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Abbrev.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part2


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable instance hexCSPairIndex_fintype (T L : ℕ) :
    Fintype (HexCSPairIndex T L) := Fintype.ofFinite _

noncomputable instance hexCSFixedIndex_fintype (T L : ℕ) (hT : 0 < T) :
    Fintype (HexCSFixedIndex T L hT) := Fintype.ofFinite _

instance hexCSPairIndex_decidableEq (T L : ℕ) :
    DecidableEq (HexCSPairIndex T L) := inferInstance

instance hexCSFixedIndex_decidableEq (T L : ℕ) (hT : 0 < T) :
    DecidableEq (HexCSFixedIndex T L hT) := inferInstance

end
end StatMech.Universality
