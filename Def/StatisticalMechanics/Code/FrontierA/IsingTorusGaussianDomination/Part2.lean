/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusGaussianDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingReflectionKernel
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Mathlib.Analysis.Calculus.Taylor
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination
open Finset Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising


variable {d k : Nat}


def IsingTorusGaussianDominated (beta : Real) : Prop :=
  ∀ h : IsingDyadicTorus d k → Real,
    isingTorusShiftedPartition beta h ≤
      isingTorusShiftedPartition (d := d) (k := k) beta 0


end StatMech.FrontierA
