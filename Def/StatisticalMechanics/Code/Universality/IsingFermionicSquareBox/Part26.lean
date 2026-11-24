module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part28


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

def fkIsingSquareLocalSmoothingGraph (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    SimpleGraph (FKIsingSquareMedialCarrier n) where
  Adj x y := ∃ d, x = .dart d ∧
    y = .dart (FKIsingMedialDart.localMate omega d)
  symm := by
    constructor
    rintro _ _ ⟨d, rfl, rfl⟩
    refine ⟨FKIsingMedialDart.localMate omega d, rfl, ?_⟩
    rw [FKIsingMedialDart.localMate_involutive]
  loopless := ⟨by
    rintro _ ⟨d, rfl, h⟩
    injection h with h
    exact FKIsingMedialDart.localMate_ne omega d h.symm⟩

end
end StatMech.Universality
