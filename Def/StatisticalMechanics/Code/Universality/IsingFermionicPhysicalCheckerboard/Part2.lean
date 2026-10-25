/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareRadialPatchDualGraph (m : Nat) :
    SimpleGraph (FKIsingSquareRadialPatchDualNode m) where
  Adj p q :=
    (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
      (p.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = p.1.2.1)
  symm := by
    constructor
    intro p q h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro p h
    rcases h.1 with h | h <;> omega


def fkIsingSquareRadialPatchDualBoundary
    (m : Nat) (p : FKIsingSquareRadialPatchDualNode m) : Prop :=
  p.1.1.1 = 0 ∨ p.1.1.1 + 1 = m ∨
    p.1.2.1 = 0 ∨ p.1.2.1 + 1 = m


def fkIsingSquareRadialPatchDualValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchDualNode m) : Real :=
  base + fkIsingSquareRadialPatchPrimitive
    n m hn hm hmpos p.1.1.1 p.1.2.1


end
end StatMech.Universality
