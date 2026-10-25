/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part2


namespace StatMech.FrontierA

def embeddingOf_functionWeakComponentwiseMaps
    {B C : Type*} (next : B -> B) (targetComponent : C -> Set B)
    (f : Set B -> B -> C)
    (htag : ∀ component x, functionWeakComponent next x = component ->
      targetComponent (f component x) = component)
    (hinj : ∀ component, Function.Injective fun
      x : {x : B // functionWeakComponent next x = component} =>
        f component x.1) : B ↪ C :=
  embeddingOf_taggedFiberwiseMaps
    (functionWeakComponent next) targetComponent f htag hinj


def crossCollision {A B C : Type*} (f : A -> C) (g : B -> C) :=
  {pair : A × B // f pair.1 = g pair.2}

end StatMech.FrontierA
