/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part2
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFullVertexGraph (n : Nat) :
    SimpleGraph (FKIsingSquareFullVertexNode n) :=
  (fkSquareBoxPlanar n).G


def fkIsingSquareFullFaceGraph (n : Nat) :
    SimpleGraph (FKIsingSquareFullFaceNode n) where
  Adj p q :=
    (p.1 = q.1 ∧ (p.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = p.2.1)) ∨
      (p.2 = q.2 ∧ (p.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = p.1.1))
  symm := by
    constructor
    rintro p q (h | h)
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro p h
    rcases h with h | h <;> rcases h.2 with h | h <;> omega


def fkIsingSquareFullVertexFixedBoundary
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Prop :=
  fkIsingSquareWiredArc n x


def fkIsingSquareFullVertexGhostMultiplicity
    (n : Nat) (x : FKIsingSquareFullVertexNode n) : Nat :=
  (if x.1 1 = -(n : Int) then 1 else 0) +
    (if x.1 0 = (n : Int) then 1 else 0) +
      (if x.1 1 = (n : Int) then 1 else 0)


def fkIsingSquareFullFaceFixedBoundary
    (n : Nat) (c : FKIsingSquareFullFaceNode n) : Prop :=
  c.2.1 = 0 ∨ c.1.1 + 1 = 2 * n ∨ c.2.1 + 1 = 2 * n


def fkIsingSquareFullFaceGhostMultiplicity
    (_n : Nat) (c : FKIsingSquareFullFaceNode _n) : Nat :=
  if c.1.1 = 0 then 1 else 0

end
end StatMech.Universality
