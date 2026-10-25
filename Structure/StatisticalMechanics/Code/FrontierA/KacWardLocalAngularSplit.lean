/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


structure KWLocalAngularData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  order : KWPortOrder G
  root : KWDartPort G -> Complex
  phase : G.Dart -> G.Dart -> Complex
  phase_eq_portRoots_of_rank_lt :
    forall (d e : G.Dart), d.snd = e.fst ->
      kwOrderedPortRank order (kwPortOfDart G d.symm) <
        kwOrderedPortRank order (kwPortOfDart G e) ->
      phase d e =
        -Complex.I * (root (kwPortOfDart G d.symm))⁻¹ *
          root (kwPortOfDart G e)
  phase_eq_portRoots_of_rank_gt :
    forall (d e : G.Dart), d.snd = e.fst ->
      kwOrderedPortRank order (kwPortOfDart G e) <
        kwOrderedPortRank order (kwPortOfDart G d.symm) ->
      phase d e =
        Complex.I * (root (kwPortOfDart G d.symm))⁻¹ *
          root (kwPortOfDart G e)
  root_ne_zero : forall p, root p ≠ 0
  root_sq_symm : forall d : G.Dart,
    root (kwPortOfDart G d.symm) ^ 2 =
      -(root (kwPortOfDart G d) ^ 2)


end StatMech.FrontierA
