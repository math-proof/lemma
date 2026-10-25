/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part4


namespace StatMech

namespace Exact3D

def PlusSubcriticalMassBridge : Prop :=
  ∀ β, β < Ising.betaC 3 →
    ∃ m, 0 < m ∧
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m


def FreeSubcriticalMassBridge : Prop :=
  ∀ β, β < Ising.betaC 3 →
    ∃ m, 0 < m ∧
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m


def PlusSubcriticalCorrelationLengthBridge : Prop :=
  ∀ β, β < Ising.betaC 3 →
    ∃ ξ, 0 < ξ ∧
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ


def FreeSubcriticalCorrelationLengthBridge : Prop :=
  ∀ β, β < Ising.betaC 3 →
    ∃ ξ, 0 < ξ ∧
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay ξ


def PlusPositiveSubcriticalMassBridge : Prop :=
  ∀ β, 0 < β → β < Ising.betaC 3 →
    ∃ m, 0 < m ∧
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay m


def FreePositiveSubcriticalMassBridge : Prop :=
  ∀ β, 0 < β → β < Ising.betaC 3 →
    ∃ m, 0 < m ∧
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay m


def PlusPositiveSubcriticalCorrelationLengthBridge : Prop :=
  ∀ β, 0 < β → β < Ising.betaC 3 →
    ∃ ξ, 0 < ξ ∧
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay ξ


def FreePositiveSubcriticalCorrelationLengthBridge : Prop :=
  ∀ β, 0 < β → β < Ising.betaC 3 →
    ∃ ξ, 0 < ξ ∧
      HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay ξ


end Exact3D
end StatMech
