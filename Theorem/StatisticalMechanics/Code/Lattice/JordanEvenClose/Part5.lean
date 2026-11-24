module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
public import Def.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem jce_reachable_of_twoOdd (hodd : jce_TwoOddReachable) (H : SimpleGraph (Site 2))
    [SimpleGraph.LocallyFinite H] (p q : Site 2)
    (hp : Odd (H.degree p)) (hq : Odd (H.degree q))
    (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) :
    H.Reachable p q :=
  hodd H p q hp hq hother

end Lattice
end StatMech
