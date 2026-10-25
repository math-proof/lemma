/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDenseIncidencePrimitiveBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveValueBridge
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDenseIncidencePrimitiveBridge
open Filter Set Topology


namespace StatMech.Universality

noncomputable section

structure FKIsingDenseIncidencePrimitivePathCompatibility
    {N : Nat -> Nat} {hN : forall k, 0 < N k} {mesh : Nat -> Real}
    (F : Nat -> Complex -> Complex)
    (D : FKIsingDenseIncidenceFamily N hN mesh) where
  steps : Nat -> Nat -> Nat
  stepLength : Nat -> Nat -> Real
  error : Nat -> Nat -> Real
  pathBound : Nat -> Real
  canonicalPath : Nat -> Nat -> Nat -> Real
  discretePath : Nat -> Nat -> Nat -> Real
  canonical_endpoint : forall j k,
    canonicalPath j k (steps j k) =
      (isingFermionicEntireSquarePrimitive (F k) (D.point j)).im
  discrete_endpoint : forall j k,
    discretePath j k (steps j k) = D.discreteVertexPrimitive j k
  base_tendsto : forall j, Tendsto
    (fun k => canonicalPath j k 0 - discretePath j k 0)
      atTop (nhds 0)
  error_tendsto : forall j, Tendsto (error j) atTop (nhds 0)
  error_nonneg : forall j k, 0 <= error j k
  pathBound_nonneg : forall j, 0 <= pathBound j
  path_length_le : forall j k,
    (steps j k : Real) * stepLength j k <= pathBound j
  increment_error : forall j k i, i < steps j k ->
    abs ((canonicalPath j k (i + 1) - canonicalPath j k i) -
      (discretePath j k (i + 1) - discretePath j k i)) <=
        stepLength j k * error j k

end
end StatMech.Universality
