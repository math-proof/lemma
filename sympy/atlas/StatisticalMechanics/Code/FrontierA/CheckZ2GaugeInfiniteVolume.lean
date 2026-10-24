/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckZ2GaugeInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume

#print axioms StatMech.FrontierA.cubicalPaddedWilsonExpectation_mono
#print axioms StatMech.FrontierA.cubicalFixedLoopWilsonSequence_tendsto
#print axioms StatMech.FrontierA.cubicalPaddedWilsonExpectation_tendsto_infiniteVolume
#print axioms StatMech.FrontierA.cubicalInfiniteVolumeWilsonExpectation_pos
#print axioms
  StatMech.FrontierA.cubicalWilsonExpectation_eq_twistedIsingPartitionRatio_of_surface
#print axioms
  StatMech.FrontierA.neg_log_cubicalPaddedWilsonExpectation_eq_disorderFreeEnergy
#print axioms
  StatMech.FrontierA.cubicalPaddedDisorderFreeEnergy_tendsto_infiniteVolume
