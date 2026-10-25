/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


def KWGraphWeightedCycleLog
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (cycleCoeff : Finset (Sym2 V) -> Complex) : Prop :=
  (forall {root : V} (p : G.Walk root root), p.IsCycle ->
      kwGraphFormalLogCoeff G phase
        (ons_finsetExponent p.edges.toFinset) =
      cycleCoeff p.edges.toFinset) /\
  (forall (S : Finset (Sym2 V)),
      kwGraphFormalLogCoeff G phase (ons_finsetExponent S) ≠ 0 ->
        exists (root : V) (p : G.Walk root root),
          p.IsCycle /\ p.edges.toFinset = S)


noncomputable def kwWeightedCycleComponentSeries
    {V I : Type u} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} (base : I -> V)
    (cycle : (i : I) -> G.Walk (base i) (base i))
    (coefficient : I -> Complex) : MvPowerSeries (Sym2 V) Complex :=
  ∑ i : I, MvPowerSeries.monomial
    (ons_finsetExponent (cycle i).edges.toFinset) (coefficient i)

end StatMech.FrontierA
