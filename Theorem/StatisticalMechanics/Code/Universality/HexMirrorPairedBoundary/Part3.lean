/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Def.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary.Part3


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


theorem hexGenuineStrip_mirrorPaired_normalized :
    hexChi⁻¹ *
      hexGenuineStripMirrorPairedData.pairedContribution = 1 :=
  hexGenuineStripMirrorPairedData.normalized_real_boundary_contribution

end StatMech.Universality
