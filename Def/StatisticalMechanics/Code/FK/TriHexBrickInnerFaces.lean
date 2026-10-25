/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickInnerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part3
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls

noncomputable section

def triHexBrickInnerCell {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1, fun k => by
    have hk := t.2 k
    exact Nat.le_trans hk (Nat.le_of_lt hNm)⟩

def triHexBrickInnerPred0 {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1 - hexagonalStep 0, by
    intro k
    have ht := t.2 k
    fin_cases k <;>
      simp [hexagonalStep] at ht ⊢ <;> omega⟩

def triHexBrickInnerPred1 {N m : Nat} (hNm : N < m)
    (t : {z : Site 2 // z ∈ box 2 N}) : TriHexPlanarFiniteCell m :=
  ⟨t.1 - hexagonalStep 1, by
    intro k
    have ht := t.2 k
    fin_cases k <;>
      simp [hexagonalStep] at ht ⊢ <;> omega⟩

end
end StatMech.FK.PeriodicPlanar
