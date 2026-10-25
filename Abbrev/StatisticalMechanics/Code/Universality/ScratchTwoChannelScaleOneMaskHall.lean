/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3


namespace StatMech.Universality

abbrev RlcScaleOneSectionA := Fin 15 → Bool

abbrev RlcScaleOneSectionB := Fin 13 → Bool

abbrev RlcScaleOneSectionC := Fin 12 → Bool

abbrev RlcScaleOnePairBlock := Fin 2 → Bool

abbrev RlcScaleOneFiveBlock := Fin 5 → Bool

abbrev RlcScaleOneUnusedBlock := Fin 3 → Bool

end StatMech.Universality
