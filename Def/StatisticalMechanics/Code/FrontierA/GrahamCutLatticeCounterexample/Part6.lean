module
public import Mathlib
public import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part5
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

def GrahamK23RootCutSupported (S : Finset (Fin 5)) : Prop :=
  let C := Finset.univ \ S
  (4 : Fin 5) ∈ C /\ ∀ v ∈ C, grahamK23ReachWithin C 4 v

end StatMech.FrontierA
