/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part8
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

def shbK4Path023 (E : Finset shbK4Edge)
    (h02 : shbK4Edge.e02 ∈ E) (h23 : shbK4Edge.e23 ∈ E) :
    (shbK4Graph E).Path 0 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons
      (shbK4Graph_adj_of_edge E shbK4Edge.e02 h02
        (x := (0 : Fin 4)) (y := 2) (by decide) (by decide))
      (SimpleGraph.Walk.cons
        (shbK4Graph_adj_of_edge E shbK4Edge.e23 h23
          (x := (2 : Fin 4)) (y := 3) (by decide) (by decide))
        SimpleGraph.Walk.nil)
  exact ⟨w, by simp [w]⟩

end StatMech.Sharpness
