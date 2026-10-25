/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoStrandCycleCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalPositiveSeamPair.Part5


namespace StatMech.FrontierD

noncomputable section

structure SixVertexDirectedSimpleArc (T : EvenTorus) where
  length : Nat
  length_pos : 0 < length
  edge : Fin length → SixVertexDirectedTorusEdge T
  head_eq_next_tail : ∀ i : Fin (length - 1),
    (edge ⟨i.val, by omega⟩).head =
      (edge ⟨i.val + 1, by omega⟩).tail
  tail_injective : Function.Injective (fun i => (edge i).tail)
  physical_injective : Function.Injective (fun i => (edge i).physical)

end
end StatMech.FrontierD
