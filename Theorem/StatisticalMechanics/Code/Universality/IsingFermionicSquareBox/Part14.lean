module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part12


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

theorem fkIsingSquareDartEndpoint_mem (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDartEndpoint n d ∈ d.1.1 := by
  rcases d with ⟨e, side⟩
  have hedge := fkIsingSquareOrientedEdge_eq n e
  rw [← hedge]
  rw [Sym2.mem_iff]
  cases side <;> simp [fkIsingSquareDartEndpoint,
    fkIsingSquareSideCorner]


end
end StatMech.Universality
