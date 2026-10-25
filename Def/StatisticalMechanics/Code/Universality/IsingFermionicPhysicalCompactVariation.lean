/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCompactVariation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteBoundaryCutoff.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCaccioppoli.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactVariation


namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section

noncomputable def fkIsingSquareRadialPatchPrimalBoundaryDistance
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Nat :=
  isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) p

noncomputable def fkIsingSquareRadialPatchDualBoundaryDistance
    (m : Nat) (hm : 2 ≤ m) (p : FKIsingSquareRadialPatchDualNode m) : Nat :=
  isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) p

noncomputable def fkIsingSquareRadialPatchPrimalTentCutoff
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat)
    (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  isingFiniteGraphBoundaryTentCutoff
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m hmpos) r p

noncomputable def fkIsingSquareRadialPatchDualTentCutoff
    (m : Nat) (hm : 2 ≤ m) (r : Nat)
    (p : FKIsingSquareRadialPatchDualNode m) : Real :=
  isingFiniteGraphBoundaryTentCutoff
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm) r p

noncomputable def fkIsingSquareRadialPatchPrimalDeepDarts
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) (r : Nat) :
    Finset (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    r ≤ fkIsingSquareRadialPatchPrimalBoundaryDistance n m hm hmpos d.snd

noncomputable def fkIsingSquareRadialPatchDualDeepDarts
    (m : Nat) (hm : 2 ≤ m) (r : Nat) :
    Finset (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    r ≤ fkIsingSquareRadialPatchDualBoundaryDistance m hm d.snd

end
end StatMech.Universality
