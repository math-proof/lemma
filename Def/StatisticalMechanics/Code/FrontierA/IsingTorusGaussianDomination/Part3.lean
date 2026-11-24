module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingReflectionKernel
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Mathlib.Analysis.Calculus.Taylor
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part2
open Finset Filter Set Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising


variable {d k : Nat}


noncomputable def isingTorusShiftedPartitionLineDeriv
    (beta : Real) (h : IsingDyadicTorus d k → Real) (t : Real) : Real :=
  ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma + t • h)) *
    (-beta * (isingTorusDirichletBilinear
      (isingTorusSpinField sigma) h + t * isingTorusDirichlet h))

end StatMech.FrontierA
