module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
public import Theorem.StatisticalMechanics.Code.Lattice.FloodFillConnected.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OutsideConnected.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InsideCoveringClose
public import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
public import Theorem.StatisticalMechanics.Code.Ising.PeierlsPlanarAssembly
open Set SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationLib.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

variable {a : Site 2}


def jsl_InteriorConnected (Vc : (hypercubicLattice 2).Walk a a) : Prop :=
  ∀ s t : Site 2, s ∈ jec_leftRegion Vc → t ∈ jec_leftRegion Vc →
      s ∉ Vc.support → t ∉ Vc.support →
    ∃ p : (hypercubicLattice 2).Walk s t, ∀ z ∈ p.support, z ∉ Vc.support


end Lattice
end StatMech
