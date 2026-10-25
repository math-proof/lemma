/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


def SurfaceDisjointCycleIsotropic {g : Nat}
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) : Prop :=
  forall {u v : V} (p : G.Walk u u) (q : G.Walk v v),
    p.IsCycle -> q.IsCycle ->
    Disjoint p.toSubgraph.verts q.toSubgraph.verts ->
    surfaceIntersection
      (surfaceSubgraphHomology edgeClass p.edges.toFinset)
      (surfaceSubgraphHomology edgeClass q.edges.toFinset) = 0

noncomputable def surfaceBaseCycleCoefficient {g : Nat} {V : Type u}
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) : Complex :=
  (surfaceParitySign
    (surfaceBaseQuadraticParity (surfaceSubgraphHomology edgeClass S)) : Real)


end StatMech.FrontierA
