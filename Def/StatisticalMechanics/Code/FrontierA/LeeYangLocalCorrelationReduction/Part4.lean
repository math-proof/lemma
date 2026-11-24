module
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangLocalCorrelationReduction.Part3
open Complex Filter MeasureTheory Metric Set Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangLocalCorrelationReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.FK StatMech.Ising StatMech.Lattice StatMech.FrontierB
  StatMech.FrontierC StatMech.Sharpness StatMech.Sharpness.FieldGhostDict


def leeYangSignedDiagonal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (q : ℂ) : LeeYangVar G → ℂ
  | Sum.inl v => if v ∈ A then -q else q
  | Sum.inr _ => 0

end StatMech.FrontierA
