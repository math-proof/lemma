/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting.Part3


namespace StatMech.FrontierD

noncomputable section

theorem positiveUnitComponentResidualTargetLift_nonempty
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (physical : SixVertexPositiveUnitComponentOrbitCover T middle
      hmiddle_pos hmiddle_lt
      (SixVertexPositiveUnitComponentResidualSources T middle
        hmiddle_pos hmiddle_lt grade))
    (hcoverage :
      SixVertexPositiveUnitComponentResidualTargetCoverage physical) :
    Nonempty
      {lift : (Σ index, (physical.data index).TargetLayer) ↪
          SixVertexHorizontalDegreeTwoHallTarget T middle
            hmiddle_pos hmiddle_lt grade //
        ∀ index target,
          sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
              T middle hmiddle_pos hmiddle_lt grade
              (lift ⟨index, target⟩) =
            physical.targetEmbedding ⟨index, target⟩} := by
  choose lift hlift using hcoverage
  let embedding : (Σ index, (physical.data index).TargetLayer) ↪
      SixVertexHorizontalDegreeTwoHallTarget T middle
        hmiddle_pos hmiddle_lt grade :=
    { toFun := fun target => lift target.1 target.2
      inj' := by
        intro first second heq
        apply physical.targetEmbedding.injective
        rw [← hlift first.1 first.2, ← hlift second.1 second.2]
        exact congrArg
          (sixVertexHorizontalDegreeTwoHallTargetPhysicalEmbedding
            T middle hmiddle_pos hmiddle_lt grade) heq }
  exact ⟨⟨embedding, hlift⟩⟩


end
end StatMech.FrontierD
