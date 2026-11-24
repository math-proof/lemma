module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
public import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
public import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
public import Def.StatisticalMechanics.Code.Lattice.WindingWitness.Part3
open SimpleGraph Function Set Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

theorem wwit_unitSquareLoop_inside_odd :
    ¬ Even (jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop) := by
  have hcount : jec_rayCount (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
    unfold wwit_unitSquareLoop
    simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
      jec_rayCount_vsegUp, jec_rayCount_hsegRight, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    norm_num
  rw [hcount]
  decide


end Lattice
end StatMech
