/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareRadialPatchPrimalGraph
    (n m : Nat) (hm : m ≤ n) :
    SimpleGraph (FKIsingSquareRadialPatchPrimalNode m) :=
  SimpleGraph.comap (fkIsingSquareRadialPatchPrimalNodeVertex n m hm)
    (fkSquareBoxPlanar n).G


def fkIsingSquareRadialPatchPrimalBoundary
    (m : Nat) (p : FKIsingSquareRadialPatchPrimalNode m) : Prop :=
  p.1.1.1 = 0 ∨ p.1.1.1 + 1 = m ∨
    p.1.2.1 = 0 ∨ p.1.2.1 + 1 = m


def fkIsingSquareRadialPatchPrimalValue
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hmpos : 0 < m)
    (base : Real) (p : FKIsingSquareRadialPatchPrimalNode m) : Real :=
  base + fkIsingSquareRadialPatchPrimitive
    n m hn hm hmpos p.1.1.1 p.1.2.1


end
end StatMech.Universality
