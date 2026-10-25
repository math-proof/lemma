/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part20


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

def coordinateReflectionSetoid (d R maxDegree maxRange : ℕ) :
    Setoid (BoundedPolymerCase d R maxDegree maxRange) where
  r := coordinateReflectionEquivalent
  iseqv := by
    constructor
    · intro c
      exact coordinateReflectionEquivalent_refl c
    · intro c c' h
      exact coordinateReflectionEquivalent_symm h
    · intro c₁ c₂ c₃ h₁₂ h₂₃
      exact coordinateReflectionEquivalent_trans h₁₂ h₂₃


end BoundedPolymerCase
end
end Exact3D
end StatMech
