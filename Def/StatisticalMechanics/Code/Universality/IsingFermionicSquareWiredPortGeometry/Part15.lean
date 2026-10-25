/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part14


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

def fkIsingSquareWiredExpandedAdj
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (x y : FKIsingSquareWiredExpandedCarrier n) : Prop :=
  (∃ a b, x = .inl a ∧ y = .inl b ∧
    (fkIsingSquareWiredSlotLocalGraph n omega).Adj a b) ∨
  (∃ a b, x = .inl a ∧ y = .inl b ∧
    ¬fkIsingSquareWiredLeftRingRemoved n a ∧
    ¬fkIsingSquareWiredLeftRingRemoved n b ∧
    (fkIsingSquareWiredSlotRingGraph n).Adj a b) ∨
  (∃ k : Fin (2 * n),
    s(x, y) = s(fkIsingSquareWiredExpandedStart n hn k, .inr k) ∨
    s(x, y) = s((.inr k : FKIsingSquareWiredExpandedCarrier n),
      fkIsingSquareWiredExpandedMiddle n hn k) ∨
    s(x, y) = s(fkIsingSquareWiredExpandedMiddle n hn k,
      fkIsingSquareWiredExpandedEnd n hn k))

end
end StatMech.Universality
