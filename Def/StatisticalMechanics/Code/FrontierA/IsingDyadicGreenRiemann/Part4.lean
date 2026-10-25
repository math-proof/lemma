/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Order.UpperLower
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part3
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

noncomputable def isingCoordinateFrequency (x : Fin d → Int) :
    StrongDual Real (IsingMomentumCoordinates d) :=
  ∑ i : Fin d, (x i : Real) •
    ContinuousLinearMap.proj i

end StatMech.FrontierA
