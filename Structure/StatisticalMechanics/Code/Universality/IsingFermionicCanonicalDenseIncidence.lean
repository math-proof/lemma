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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCanonicalDenseIncidence.Part7
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

structure FKIsingCanonicalDensePrimitiveLocalInputs
    (F : Nat → Complex → Complex) where
  canonicalPath : Nat → Nat → Nat → Real
  discretePath : Nat → Nat → Nat → Real
  error : Nat → Nat → Real
  canonical_endpoint : ∀ j k,
    canonicalPath j k
        (fkIsingDenseRationalPathSteps
          (fkIsingRationalPairEnumeration j) k) =
      (isingFermionicEntireSquarePrimitive
        (F k) (fkIsingDenseRationalPoint j)).im
  discrete_endpoint : ∀ j k,
    discretePath j k
        (fkIsingDenseRationalPathSteps
          (fkIsingRationalPairEnumeration j) k) =
      fkIsingExpandingSquareDenseIncidenceFamily.discreteVertexPrimitive j k
  base_tendsto : ∀ j, Tendsto
    (fun k ↦ canonicalPath j k 0 - discretePath j k 0)
    atTop (nhds 0)
  error_tendsto : ∀ j, Tendsto (error j) atTop (nhds 0)
  error_nonneg : ∀ j k, 0 ≤ error j k
  increment_error : ∀ j k i,
    i < fkIsingDenseRationalPathSteps
        (fkIsingRationalPairEnumeration j) k →
      abs ((canonicalPath j k (i + 1) - canonicalPath j k i) -
        (discretePath j k (i + 1) - discretePath j k i)) ≤
          (2 * fkIsingExpandingSquareScale k) * error j k

end
end StatMech.Universality
