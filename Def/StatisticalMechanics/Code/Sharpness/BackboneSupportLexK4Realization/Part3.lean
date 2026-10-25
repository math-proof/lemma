/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part2
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

noncomputable def shbK4GraphEdgeEquiv (E : Finset shbK4Edge) :
    ↑E ≃ ↑(shbK4Graph E).edgeFinset where
  toFun k := ⟨k.1.code, by
    rw [shbK4Graph_edgeFinset]
    exact Finset.mem_image.mpr ⟨k.1, k.2, rfl⟩⟩
  invFun e := ⟨Classical.choose (Finset.mem_image.mp (by
    simpa [shbK4Graph_edgeFinset] using e.2)),
    (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using e.2))).1⟩
  left_inv k := by
    apply Subtype.ext
    exact shbK4Edge.code_injective
      (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using
          ((⟨k.1.code, by
              rw [shbK4Graph_edgeFinset]
              exact Finset.mem_image.mpr ⟨k.1, k.2, rfl⟩⟩ :
            ↑(shbK4Graph E).edgeFinset)).2))).2
  right_inv e := by
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.mem_image.mp (by
      simpa [shbK4Graph_edgeFinset] using e.2))).2


def shbK4DirectPath (E : Finset shbK4Edge)
    (h03 : shbK4Edge.e03 ∈ E) : (shbK4Graph E).Path (0 : Fin 4) 3 := by
  let w : (shbK4Graph E).Walk (0 : Fin 4) 3 :=
    SimpleGraph.Walk.cons (by
      rw [shbK4Graph, SimpleGraph.fromEdgeSet_adj]
      constructor
      · exact Finset.mem_image.mpr ⟨shbK4Edge.e03, h03, rfl⟩
      · decide)
      SimpleGraph.Walk.nil
  exact ⟨w, by simp [w]⟩

end StatMech.Sharpness
