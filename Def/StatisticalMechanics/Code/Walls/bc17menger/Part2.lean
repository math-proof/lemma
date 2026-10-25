/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Theorem.StatisticalMechanics.Code.Walls.bc17menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


def bc17_botFamily {A B : Set V} {k : ℕ} {f : Fin k → V} (hinj : Function.Injective f)
    (hf : ∀ i, f i ∈ A ∩ B) : bc16_DisjointPathFamily (⊥ : SimpleGraph V) A B (Fin k) where
  a := f
  b := f
  p := fun _ => Walk.nil
  ha := fun i => (hf i).1
  hb := fun i => (hf i).2
  hp := fun _ => Walk.IsPath.nil
  hdisj := by
    intro i j hij x hx hx'
    rw [Walk.support_nil, List.mem_singleton] at hx hx'
    exact hij (hinj (hx.symm.trans hx'))

end StatMech.Walls
