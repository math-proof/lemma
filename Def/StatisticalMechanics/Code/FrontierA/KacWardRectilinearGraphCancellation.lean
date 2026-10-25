/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearGraphCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFixedMonomialCancellation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

noncomputable def kwGraphNonbacktrackingFactor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.Dart -> G.Dart -> ℂ := by
  classical
  exact fun dart next =>
    if G.DartAdj dart next ∧ dart.edge ≠ next.edge then 1 else 0


end StatMech.FrontierA
