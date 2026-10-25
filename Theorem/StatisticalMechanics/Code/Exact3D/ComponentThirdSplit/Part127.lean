/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part138
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryCrossingCapUpperBound_pairCountMultiplicity :
    BoundaryCrossingCapUpperBoundPositiveSubcritical
      boundaryCrossingCapPairCountMultiplicityBound := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  simp [boundaryCrossingCap, boundaryCrossingCapPairCountMultiplicityBound]

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoundNonnegative_pairCountMultiplicity :
    BoundaryCrossingCapBoundNonnegativePositiveSubcritical
      boundaryCrossingCapPairCountMultiplicityBound := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  simpa [boundaryCrossingCapPairCountMultiplicityBound, Ωnz] using
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
      Ωnz

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoundLe_pairCountMultiplicity_sourceSectorMultiplicitySquare :
    BoundaryCrossingCapBoundLePositiveSubcritical
      boundaryCrossingCapPairCountMultiplicityBound
      boundaryCrossingCapSourceSectorMultiplicitySquareBound := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  simpa [
    boundaryCrossingCapPairCountMultiplicityBound,
    boundaryCrossingCapSourceSectorMultiplicitySquareBound,
    Ωnz] using
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_le_sourceSectorMultiplicitySquare
      Ωnz

set_option linter.style.longLine false in


theorem boundaryCrossingCapUpperBound_sourceSectorMultiplicitySquare :
    BoundaryCrossingCapUpperBoundPositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  simpa [boundaryCrossingCap, boundaryCrossingCapSourceSectorMultiplicitySquareBound,
    Ωnz] using
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_le_sourceSectorMultiplicitySquare
      Ωnz

set_option linter.style.longLine false in


theorem boundaryCrossingCapBoundNonnegative_sourceSectorMultiplicitySquare :
    BoundaryCrossingCapBoundNonnegativePositiveSubcritical
      boundaryCrossingCapSourceSectorMultiplicitySquareBound := by
  intro β _hβpos _hβc
  filter_upwards [] with n
  intro H _hH Ω
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  simpa [Ωnz] using
    boundaryCrossingCapSourceSectorMultiplicitySquareBound_nonneg
      β H Ωnz


end Exact3D
end StatMech
