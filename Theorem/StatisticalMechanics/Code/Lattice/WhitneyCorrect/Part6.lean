module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
public import Macro.StatisticalMechanics.Code.Lattice.WhitneyCorrect
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem whc_inv_bottom (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(0:ℤ), 0], ![1, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
  whc_prove_inv


theorem whc_inv_right (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(1:ℤ), 0], ![1, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
  whc_prove_inv


theorem whc_inv_top (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(1:ℤ), 1], ![0, 1]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) := by
  whc_prove_inv


theorem whc_inv_left (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b = s(![(0:ℤ), 1], ![0, 0]) ↔ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0]) := by
  whc_prove_inv


end Lattice
end StatMech
