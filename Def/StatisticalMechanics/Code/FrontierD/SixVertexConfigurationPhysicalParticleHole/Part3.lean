/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexConfigurationPhysicalParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalPairedBranch.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexConfigurationPhysicalParticleHole.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPhysicalParticleHoleSourceEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width} :
    SixVertexConfigurationPhysicalSource T
        (sixVertexPhysicalParticleHoleMiddle middle)
        (sixVertexPhysicalParticleHoleMiddle_pos middle hmiddle_lt)
        (sixVertexPhysicalParticleHoleMiddle_lt middle hmiddle_pos) ↪
      SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt where
  toFun source :=
    (⟨sixVertexArrowsComplement source.2.1,
      sixVertexArrowsComplement_iceRule source.2.2.1, by
        change sixVertexUpCount (fun i =>
          !source.2.1.vertical (i, svFinLast T.height_pos)) = middle.val - 1
        rw [sixVertexUpCount_complement]
        have hsector := source.2.2.2
        change sixVertexUpCount (fun i =>
          source.2.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
        rw [hsector]
        simp [sixVertexPhysicalParticleHoleMiddle]
        omega⟩,
      ⟨sixVertexArrowsComplement source.1.1,
        sixVertexArrowsComplement_iceRule source.1.2.1, by
          change sixVertexUpCount (fun i =>
            !source.1.1.vertical (i, svFinLast T.height_pos)) = middle.val + 1
          rw [sixVertexUpCount_complement]
          have hsector := source.1.2.2
          change sixVertexUpCount (fun i =>
            source.1.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
          rw [hsector]
          simp [sixVertexPhysicalParticleHoleMiddle]
          omega⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.2.1) heq
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.1.1) heq

def sixVertexPhysicalParticleHoleTargetEmbedding
    {T : EvenTorus} {middle : Fin (T.width + 1)} :
    SixVertexConfigurationPhysicalTarget T middle ↪
      SixVertexConfigurationPhysicalTarget T
        (sixVertexPhysicalParticleHoleMiddle middle) where
  toFun target :=
    (⟨sixVertexArrowsComplement target.1.1,
      sixVertexArrowsComplement_iceRule target.1.2.1, by
        change sixVertexUpCount (fun i =>
          !target.1.1.vertical (i, svFinLast T.height_pos)) =
            T.width - middle.val
        rw [sixVertexUpCount_complement]
        have hsector := target.1.2.2
        change sixVertexUpCount (fun i =>
          target.1.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
        rw [hsector]⟩,
      ⟨sixVertexArrowsComplement target.2.1,
        sixVertexArrowsComplement_iceRule target.2.2.1, by
          change sixVertexUpCount (fun i =>
            !target.2.1.vertical (i, svFinLast T.height_pos)) =
              T.width - middle.val
          rw [sixVertexUpCount_complement]
          have hsector := target.2.2.2
          change sixVertexUpCount (fun i =>
            target.2.1.vertical (i, svFinLast T.height_pos)) = _ at hsector
          rw [hsector]⟩)
  inj' := by
    intro first second heq
    apply Prod.ext
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.1.1) heq
    · apply Subtype.ext
      apply sixVertexArrowsComplement_injective
      exact congrArg (fun pair => pair.2.1) heq

end
end StatMech.FrontierD
