/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part6
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

def FiniteBoundaryGhostFactorDictionaryPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∃ (base obs limitFactor : BoundaryGhostConfig 3 n → ℝ)
        (factor : ℝ → BoundaryGhostConfig 3 n → ℝ),
        FiniteBoundaryGhostFactorDictionary 3 n β
          base obs limitFactor factor


def FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical : Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∃ (base obs : BoundaryGhostConfig 3 n → ℝ),
        FiniteBoundaryGhostCountFactorDictionary 3 n β base obs


def FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      FiniteBoundaryGhostAlignedLimitIdentification 3 n β


end Exact3D
end StatMech
