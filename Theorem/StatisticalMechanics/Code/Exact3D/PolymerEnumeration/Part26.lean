/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PolymerEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.PolymerEnumeration.Part32


namespace StatMech

namespace Exact3D

open StatMech.Lattice

noncomputable section

namespace BoundedPolymerCase

@[simp] theorem mem_cubicOrbitFiber {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange} :
    c' ∈ cubicOrbitFiber c ↔ cubicEquivalent c' c := by
  simp [cubicOrbitFiber]


theorem cubicOrbitFiber_nonempty {d R maxDegree maxRange : ℕ}
    (c : BoundedPolymerCase d R maxDegree maxRange) :
    (cubicOrbitFiber c).Nonempty := by
  exact ⟨c, by simp [cubicOrbitFiber]⟩


theorem cubicOrbitFiber_eq_of_equivalent {d R maxDegree maxRange : ℕ}
    {c c' : BoundedPolymerCase d R maxDegree maxRange}
    (h : cubicEquivalent c c') :
    cubicOrbitFiber c = cubicOrbitFiber c' := by
  ext x
  constructor
  · intro hx
    exact mem_cubicOrbitFiber.mpr
      (cubicEquivalent_trans (mem_cubicOrbitFiber.mp hx) h)
  · intro hx
    exact mem_cubicOrbitFiber.mpr
      (cubicEquivalent_trans (mem_cubicOrbitFiber.mp hx)
        (cubicEquivalent_symm h))


end BoundedPolymerCase
end
end Exact3D
end StatMech
