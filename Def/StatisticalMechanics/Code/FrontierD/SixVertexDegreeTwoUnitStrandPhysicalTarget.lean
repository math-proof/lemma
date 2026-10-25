/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitStrandPhysicalTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoStrandCycleFlip
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionCyclePhysicalRepair.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexDegreeTwoUnitStrandPhysicalTarget
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    (source : SixVertexConfigurationPhysicalSource T middle
      hmiddle_pos hmiddle_lt)
    (hdegree : SixVertexLocallyDegreeTwo source.1.1 source.2.1)
    (seed : SixVertexOrientedDisagreementDart source.1.1 source.2.1)
    (hunit : (sixVertexDegreeTwoStrandSeamWord source.1.2.1
      source.2.2.1 hdegree seed).sum = 1) :
    SixVertexConfigurationPhysicalTarget T middle := by
  let mask := (sixVertexDegreeTwoStrandDirectedSimpleCycle
    source.1.2.1 source.2.2.1 hdegree seed).mask
  have hfirstIce : (sixVertexTorusFlip mask source.1.1).IceRule :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_ice
      source.1.2.1 source.2.2.1 hdegree seed
  have hsecondIce : (sixVertexTorusFlip mask source.2.1).IceRule :=
    sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_ice
      source.1.2.1 source.2.2.1 hdegree seed
  have hfirstInt :
      (sixVertexUpCount (svTorusVerticalRows T
        (sixVertexTorusFlip mask source.1.1)
        (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [sixVertexTorusFlip_upCount,
      sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_seamDelta_eq_wordSum,
      hunit, source.1.2.2]
    push_cast
    omega
  have hsecondInt :
      (sixVertexUpCount (svTorusVerticalRows T
        (sixVertexTorusFlip mask source.2.1)
        (svFinLast T.height_pos)) : Int) = middle.val := by
    rw [sixVertexTorusFlip_upCount,
      sixVertexDegreeTwoStrandDirectedSimpleCycle_flip_second_seamDelta,
      hunit, source.2.2.2]
    push_cast
    omega
  exact
    (⟨sixVertexTorusFlip mask source.1.1, hfirstIce,
      by exact_mod_cast hfirstInt⟩,
    ⟨sixVertexTorusFlip mask source.2.1, hsecondIce,
      by exact_mod_cast hsecondInt⟩)

end
end StatMech.FrontierD
