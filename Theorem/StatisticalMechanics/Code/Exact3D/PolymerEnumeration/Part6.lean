/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part7


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

theorem stableKey_injective {d R maxDegree maxRange : ℕ} :
    Function.Injective (@stableKey d R maxDegree maxRange) := by
  intro c c' h
  have hpair :
      (supportKey c.support, toLex (c.degree, c.range)) =
        (supportKey c'.support, toLex (c'.degree, c'.range)) := by
    simpa [stableKey] using congrArg ofLex h
  have hsuppKey : supportKey c.support = supportKey c'.support :=
    congrArg Prod.fst hpair
  have hdegRangeLex : toLex (c.degree, c.range) = toLex (c'.degree, c'.range) :=
    congrArg Prod.snd hpair
  have hdegRange : (c.degree, c.range) = (c'.degree, c'.range) := by
    simpa using congrArg ofLex hdegRangeLex
  cases c
  cases c'
  simp only at hsuppKey hdegRange ⊢
  have hsupp := supportKey_injective hsuppKey
  cases hdegRange
  cases hsupp
  rfl


end BoundedPolymerCase
end
end Exact3D
end StatMech
