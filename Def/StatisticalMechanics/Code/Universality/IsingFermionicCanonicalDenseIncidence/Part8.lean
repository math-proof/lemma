/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCanonicalDenseIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

namespace FKIsingCanonicalDensePrimitiveLocalInputs

noncomputable def toPathCompatibility
    {F : Nat → Complex → Complex}
    (L : FKIsingCanonicalDensePrimitiveLocalInputs F) :
    FKIsingDenseIncidencePrimitivePathCompatibility
      (N := fkIsingExpandingSquareSide)
      (hN := fkIsingExpandingSquareSide_pos)
      (mesh := fkIsingExpandingSquareScale) F
      fkIsingExpandingSquareDenseIncidenceFamily where
  steps j k := fkIsingDenseRationalPathSteps
    (fkIsingRationalPairEnumeration j) k
  stepLength _ k := 2 * fkIsingExpandingSquareScale k
  error := L.error
  pathBound j := 2 *
    (|(((fkIsingRationalPairEnumeration j).1 : Real) +
          ((fkIsingRationalPairEnumeration j).2 : Real)) / 2| +
      |(((fkIsingRationalPairEnumeration j).1 : Real) -
          ((fkIsingRationalPairEnumeration j).2 : Real)) / 2| + 2)
  canonicalPath := L.canonicalPath
  discretePath := L.discretePath
  canonical_endpoint := L.canonical_endpoint
  discrete_endpoint := L.discrete_endpoint
  base_tendsto := L.base_tendsto
  error_tendsto := L.error_tendsto
  error_nonneg := L.error_nonneg
  pathBound_nonneg j := by positivity
  path_length_le j k := by
    exact fkIsingDenseRationalPath_length_le
      (fkIsingRationalPairEnumeration j) k
  increment_error := L.increment_error

end FKIsingCanonicalDensePrimitiveLocalInputs
end
end StatMech.Universality
