module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareScaledDomain.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer.Part8
public import Theorem.StatisticalMechanics.Code.Universality.FiniteHolomorphicInterpolation
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBoundaryScaledDomain.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingSquareBoundaryPerturbedRawInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (z : Complex) : Complex :=
  if h : ∃ a : FKIsingSquareWiredCarrier n,
      fkIsingSquareWiredPerturbedCarrierPosition n hn mesh hmesh a = z then
    (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
      (Classical.choose h)
  else 0

end
end StatMech.Universality
