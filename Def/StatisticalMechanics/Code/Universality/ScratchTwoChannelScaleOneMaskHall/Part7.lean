/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part4


namespace StatMech.Universality

def rlcScaleOneRouteClass (omega : RlcScaleOneEdgeConfig) : Fin 4 :=
  if omega 6 = false then 0
  else if omega 11 = false ∧ omega 7 = false then 1
  else if omega 9 = false ∧ omega 7 = false then 2
  else 3

def rlcScaleOneRestrictA (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionA :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 7, omega 8, omega 9, omega 10, omega 11, omega 12,
    omega 13, omega 14, omega 15]

def rlcScaleOneRestrictB (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionB :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 8, omega 9, omega 10, omega 12, omega 13, omega 14,
    omega 15]

def rlcScaleOneRestrictC (omega : RlcScaleOneEdgeConfig) :
    RlcScaleOneSectionC :=
  ![omega 0, omega 1, omega 2, omega 3, omega 4, omega 5,
    omega 8, omega 10, omega 12, omega 13, omega 14, omega 15]

def rlcScaleOneRestrictD (omega : RlcScaleOneEdgeConfig) : Fin 12 → Bool :=
  ![omega 0, omega 1, omega 3, omega 4, omega 7, omega 9,
    omega 10, omega 11, omega 12, omega 13, omega 14, omega 15]

end StatMech.Universality
