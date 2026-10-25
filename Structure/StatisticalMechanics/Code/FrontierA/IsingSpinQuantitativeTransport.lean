/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinQuantitativeTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinMovingMesh.Part4
open Filter Topology


namespace StatMech.FrontierA

open StatMech StatMech.FK StatMech.Ising


structure SpinConformalTransportEstimate
    {ι : Type*} [Fintype ι]
    (Φ : Complex → Complex) (a : ι → Complex)
    (source target : Nat → Real) where
  discreteDerivative : Nat → ι → Complex
  error : Nat → Real
  error_tendsto : Tendsto error atTop (nhds 0)
  derivative_error_le : ∀ n i,
    dist (discreteDerivative n i) (deriv Φ (a i)) ≤ error n
  correlation_error_le : ∀ n,
    |target n - spinDerivativeFactor (discreteDerivative n) * source n| ≤ error n

end StatMech.FrontierA
