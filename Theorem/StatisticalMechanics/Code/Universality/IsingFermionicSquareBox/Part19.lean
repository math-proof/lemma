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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part17


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareDartDirection_available (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d)
      (fkIsingSquareDartDirection n d) := by
  rcases d with ⟨e, side⟩
  have bt0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 0
  have bt1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).tail 1
  have bh0 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).head 0
  have bh1 := fkIsingSquareVertex_coordinate_bounds n
    (fkIsingSquareOrientedEdge n e).head 1
  have step := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;> cases side <;>
    simp [fkIsingSquareDartDirection, fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner, fkIsingSquareDirectionAvailable,
      haxis] at step ⊢
  all_goals
    try have h0 := congrFun step 0
    try have h1 := congrFun step 1
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    try change (fkIsingSquareOrientedEdge n e).head.1 0 =
      (fkIsingSquareOrientedEdge n e).tail.1 0 + 1 at h0
    try change (fkIsingSquareOrientedEdge n e).head.1 0 =
      (fkIsingSquareOrientedEdge n e).tail.1 0 at h0
    try change (fkIsingSquareOrientedEdge n e).head.1 1 =
      (fkIsingSquareOrientedEdge n e).tail.1 1 + 1 at h1
    try change (fkIsingSquareOrientedEdge n e).head.1 1 =
      (fkIsingSquareOrientedEdge n e).tail.1 1 at h1
    omega


end
end StatMech.Universality
