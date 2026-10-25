/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardFlatSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardReversibleCycleCoefficient.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u


structure SurfaceFlatSpinorEmbedding (g : Nat)
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  phase : G.Dart -> G.Dart -> Complex
  edgeClass : Sym2 V -> SurfaceHomology g
  localIntersection : Sym2 V -> Sym2 V -> Fin 2
  degree_le_three : forall vertex, G.degree vertex <= 3
  phase_reverse : forall dart next,
    G.DartAdj dart next -> dart.edge ≠ next.edge ->
      phase next.symm dart.symm = (phase dart next)⁻¹
  path_phase_sq : forall {N : Nat} (path : Fin (N + 1) -> G.Dart),
    path (Fin.last N) = (path 0).symm ->
      (forall j : Fin N,
        G.DartAdj (path j.castSucc) (path j.succ) /\
          (path j.castSucc).edge ≠ (path j.succ).edge) ->
      (∏ j : Fin N,
        phase (path j.castSucc) (path j.succ)) ^ 2 = -1
  closed_phase_sq : forall {n : Nat} [NeZero n]
      (loop : Fin n -> G.Dart),
    (forall k : Fin n,
      G.DartAdj (loop k) (loop (k + 1)) /\
        (loop k).edge ≠ (loop (k + 1)).edge) ->
      (∏ k, phase (loop k) (loop (k + 1))) ^ 2 = 1
  simple_cycle_spin_holonomy : forall {root : V}
      (p : G.Walk root root) (hp : p.IsCycle),
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
      -(surfaceBaseCycleCoefficient edgeClass p.edges.toFinset)
  intersection_formula : forall (F K : Finset (Sym2 V)),
    surfaceIntersection
        (surfaceSubgraphHomology edgeClass F)
        (surfaceSubgraphHomology edgeClass K) =
      ∑ edge ∈ F, ∑ other ∈ K,
        localIntersection edge other
  localIntersection_zero : forall (edge other : Sym2 V),
    Disjoint edge.toFinset other.toFinset ->
      localIntersection edge other = 0

end StatMech.FrontierA
