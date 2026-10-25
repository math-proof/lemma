/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample
open Finset


namespace StatMech.FrontierA

def grahamC4ReachWithin (C : Finset (Fin 4)) (u v : Fin 4) : Prop :=
  u ∈ C /\ v ∈ C /\
    (u = v \/ grahamC4Adj u v \/
      (∃ a ∈ C, grahamC4Adj u a /\ grahamC4Adj a v) \/
      (∃ a ∈ C, ∃ b ∈ C,
        grahamC4Adj u a /\ grahamC4Adj a b /\ grahamC4Adj b v))

end StatMech.FrontierA
