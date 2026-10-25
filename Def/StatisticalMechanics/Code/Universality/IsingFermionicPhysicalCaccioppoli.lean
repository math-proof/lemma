/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCaccioppoli.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteCutoff
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalPrimitiveBounds
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCaccioppoli


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareRadialPatchPrimalInteriorCutoff
    (m : Nat) (p : FKIsingSquareRadialPatchPrimalNode m) : Real := by
  classical
  exact if fkIsingSquareRadialPatchPrimalBoundary m p then 0 else 1


noncomputable def fkIsingSquareRadialPatchDualInteriorCutoff
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) : Real := by
  classical
  exact if fkIsingSquareRadialPatchDualBoundary m p then 0 else 1


noncomputable def fkIsingSquareRadialPatchPrimalInteriorDarts
    (n m : Nat) (hm : m ≤ n) :
    Finset (fkIsingSquareRadialPatchPrimalGraph n m hm).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    fkIsingSquareRadialPatchPrimalInteriorCutoff m d.snd = 1


noncomputable def fkIsingSquareRadialPatchDualInteriorDarts
    (m : Nat) : Finset (fkIsingSquareRadialPatchDualGraph m).Dart := by
  classical
  exact Finset.univ.filter fun d ↦
    fkIsingSquareRadialPatchDualInteriorCutoff m d.snd = 1

end
end StatMech.Universality
