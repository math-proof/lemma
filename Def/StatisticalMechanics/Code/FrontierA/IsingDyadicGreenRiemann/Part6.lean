module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenLowMomentum
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.MeasureTheory.Order.UpperLower
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part5
open Bornology Filter Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate Pointwise Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenRiemann.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

variable {d : Nat}

open Lattice

noncomputable def isingRegularizedCoordinateGreenComplex
    (eta : Real) : StrongDual Real (IsingMomentumCoordinates d) → Complex :=
  fun w => ∫ q, Real.fourierChar (-w q) •
    isingRegularizedCoordinateDensity eta q

end StatMech.FrontierA
