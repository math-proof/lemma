/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part4
open Finset


namespace StatMech.FrontierA

def grahamK23ReachWithin (C : Finset (Fin 5)) (u v : Fin 5) : Prop :=
  u ∈ C /\ v ∈ C /\
    (u = v \/ grahamK23Adj u v \/
      (∃ a ∈ C, grahamK23Adj u a /\ grahamK23Adj a v) \/
      (∃ a ∈ C, ∃ b ∈ C,
        grahamK23Adj u a /\ grahamK23Adj a b /\ grahamK23Adj b v) \/
      (∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C,
        grahamK23Adj u a /\ grahamK23Adj a b /\
          grahamK23Adj b c /\ grahamK23Adj c v))

end StatMech.FrontierA
