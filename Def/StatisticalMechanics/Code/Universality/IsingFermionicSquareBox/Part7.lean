module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredExteriorStar (n : Nat) :
    SimpleGraph (fkSquareBoxPlanar n).V where
  Adj x y := x ≠ y ∧ fkIsingSquareWiredArc n x ∧
    fkIsingSquareWiredArc n y ∧
      (x = fkIsingSquareMarkedA n ∨ y = fkIsingSquareMarkedA n)
  symm := by
    constructor
    rintro x y ⟨hne, hx, hy, hroot⟩
    exact ⟨hne.symm, hy, hx, hroot.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end
end StatMech.Universality
