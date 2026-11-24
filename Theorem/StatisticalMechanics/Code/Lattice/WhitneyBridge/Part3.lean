module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
public import Def.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part2
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

theorem whb_correctModel_square_separates :
    (∀ g, ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g) ∧
      ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite :=
  ⟨whb_faceRegion_interior_isolated, whb_faceRegion_interior_bounded⟩


theorem whb_loop_crossing_even (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  crossCount_even_of_loop S w


theorem whb_barrier_separates (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) (w : (hypercubicLattice 2).Walk x y) :
    ¬ Even (crossCount S w) :=
  crossCount_odd_of_separated S hx hy w


theorem whb_latticeMinusBarrier_separates (S : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ S) (hy : y ∉ S) :
    ¬ (latticeMinusBarrier S).Reachable x y :=
  not_reachable_latticeMinusBarrier S hx hy

end Lattice
end StatMech
