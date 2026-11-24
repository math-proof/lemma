module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyBridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

noncomputable def whb_faceRegion (G : SimpleGraph (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet
  symm := by
    constructor
    intro f g ⟨hadj, hs⟩
    exact ⟨hadj.symm, by rwa [sharedPrimalEdge_comm_of_adj hadj] at hs⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech
