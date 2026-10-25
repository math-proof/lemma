/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def kwGraphTransition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : Sym2 V -> ℂ) (phase : G.Dart -> G.Dart -> ℂ) :
    Matrix G.Dart G.Dart ℂ :=
  fun d e =>
    if d.snd = e.fst ∧ d.edge ≠ e.edge then x d.edge * phase d e else 0


end StatMech.FrontierA
