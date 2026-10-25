/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Inductive.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part2


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredExteriorGadget (n : Nat) :
    SimpleGraph (FKIsingSquareWiredGadgetVertex n) where
  Adj x y :=
    (∃ v, fkIsingSquareWiredArc n v ∧
      x = .exteriorRoot ∧ y = .physical v) ∨
    (∃ v, fkIsingSquareWiredArc n v ∧
      y = .exteriorRoot ∧ x = .physical v)
  symm := by
    constructor
    intro x y h
    rcases h with ⟨v, hv, rfl, rfl⟩ | ⟨v, hv, rfl, rfl⟩
    · exact Or.inr ⟨v, hv, rfl, rfl⟩
    · exact Or.inl ⟨v, hv, rfl, rfl⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨v, _, hroot, hphysical⟩ |
      ⟨v, _, hroot, hphysical⟩ <;>
      cases hroot <;> cases hphysical⟩


def fkIsingSquareLiftPhysicalGraph (n : Nat)
    (H : SimpleGraph (fkSquareBoxPlanar n).V) :
    SimpleGraph (FKIsingSquareWiredGadgetVertex n) where
  Adj x y := ∃ u v, x = .physical u ∧ y = .physical v ∧ H.Adj u v
  symm := by
    constructor
    rintro x y ⟨u, v, rfl, rfl, huv⟩
    exact ⟨v, u, rfl, rfl, huv.symm⟩
  loopless := ⟨by
    rintro x ⟨u, v, hx, hy, huv⟩
    subst x
    cases hy
    exact H.irrefl huv⟩


def fkIsingSquareWiredGadgetProjection (n : Nat) :
    FKIsingSquareWiredGadgetVertex n → (fkSquareBoxPlanar n).V
  | .physical v => v
  | .exteriorRoot => fkIsingSquareMarkedA n


end
end StatMech.Universality
