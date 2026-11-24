module
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
public import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part3
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

def KWGraphShiftedSimpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) : Prop :=
  ∀ {root : V} (p : G.Walk root root), (hp : p.IsCycle) ->
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
      -surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset

end StatMech.FrontierA
