/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentResidualRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part12
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentResidualRouting


namespace StatMech.FrontierD

noncomputable section

structure SixVertexPositiveUnitComponentResidualWitness
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width}
    {grade : Nat × Nat}
    (source : SixVertexHorizontalDegreeTwoHallSource T middle
      hmiddle_pos hmiddle_lt grade) where
  k : Nat
  base : SixVertexPositiveUnitComponentOrbitBase T middle k
  positive : BooleanLayer
    (SixVertexDisagreementComponent base.first base.second) (k + 1)
  source_eq : base.source positive hmiddle_pos hmiddle_lt =
    (sixVertexHorizontalActualDeficitConfigurationPair source).1


end
end StatMech.FrontierD
