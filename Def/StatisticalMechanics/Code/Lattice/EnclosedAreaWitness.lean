module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def eaw_InteriorSubset (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ z : Site 2, ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) → z ∈ K


end Lattice
end StatMech
