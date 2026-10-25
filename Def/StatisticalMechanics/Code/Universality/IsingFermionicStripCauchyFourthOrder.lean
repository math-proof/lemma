/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStripCauchyFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCompactPlacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVariableFourthOrderBulk.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSpatialResidualComparison.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRadialShellCardinality.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStripCauchyFourthOrder
open Metric


namespace StatMech.Universality

open Metric

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def unitStripHalfBallFourthTensorBound (d : Real) : NNReal :=
  ⟨12288 / d ^ 4, by positivity⟩

noncomputable def verticalOscillationHalfBallFourthTensorBound
    (C : NNReal) (d : Real) : NNReal :=
  ⟨12288 * (C : Real) / d ^ 4, by positivity⟩


noncomputable def unitStripCenteredBallFourthOrderResidualBound
    (h d : Real) : Real :=
  ((4 * (unitStripHalfBallFourthTensorBound d : Real)) +
      4 * (unitStripHalfBallFourthTensorBound d : Real)) * |h| ^ 4 / 12

noncomputable def verticalOscillationCenteredBallFourthOrderResidualBound
    (C : NNReal) (h d : Real) : Real :=
  ((4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) +
      4 * (verticalOscillationHalfBallFourthTensorBound C d : Real)) *
    |h| ^ 4 / 12

end FKIsingSquareBoundaryLayerCoordinateOneForm
end StatMech.Universality
