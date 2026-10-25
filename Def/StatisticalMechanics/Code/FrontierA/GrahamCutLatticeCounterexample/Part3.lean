/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part2
open Finset


namespace StatMech.FrontierA

def GrahamC4RootCutSupported (S : Finset (Fin 4)) : Prop :=
  let C := Finset.univ \ S
  (3 : Fin 4) ∈ C /\ ∀ v ∈ C, grahamC4ReachWithin C 3 v

end StatMech.FrontierA
