module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.JordanCrossingCount.Part7
open SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem jwc_faceAdj_NE_NW (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c, d] ![c - 1, d] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_NW_SW (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c - 1, d] ![c - 1, d - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_SW_SE (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c - 1, d - 1] ![c, d - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega

theorem jwc_faceAdj_SE_NE (c d : ℤ) :
    (hypercubicLattice 2).Adj ![c, d - 1] ![c, d] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; omega


end Lattice
end StatMech
