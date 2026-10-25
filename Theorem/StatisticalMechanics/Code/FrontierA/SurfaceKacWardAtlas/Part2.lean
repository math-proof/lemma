/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry.Part3
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardAtlas.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u


theorem surfaceParitySign_one_add (z : Fin 2) :
    (surfaceParitySign (1 + z) : Complex) =
      -(surfaceParitySign z : Complex) := by
  fin_cases z <;> norm_num [surfaceParitySign, Fin.val_add]


theorem ClosedFlatSurfaceGraphAtlas.simple_cycle_holonomy
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (atlas : ClosedFlatSurfaceGraphAtlas g G)
    (hadmissible : atlas.AdmissibleConeAngles)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct atlas.phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient atlas.edgeClass p.edges.toFinset) := by
  rw [atlas.developed_phase_product p hp, hadmissible p hp]
  unfold surfaceBaseCycleCoefficient
  exact surfaceParitySign_one_add _


end StatMech.FrontierA
