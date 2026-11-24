module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
public import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
public import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Walls.jc8core.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
public import Theorem.StatisticalMechanics.Code.Walls.jc9core
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.Lattice


def jc9_InteriornessInputs (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (z0 : Site 2) : Prop :=
  (∀ z, z ∉ K → ∃ z1 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z1,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧
      (∀ q ∈ (mpl_orbitLoop K a).support, z1 0 ≤ q 0)) ∧
  z0 ∈ K ∧
  (¬ Even (jec_rayCount z0 (mpl_orbitLoop K a))) ∧
  (∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0,
      (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support))


end Walls
end StatMech
