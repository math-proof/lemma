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
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination
open Finset Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising


variable {d k : Nat}


def isingTorusStep (i : Fin d) : IsingDyadicTorus d k :=
  Pi.single i 1


noncomputable def isingTorusDirichletBilinear
    (u v : IsingDyadicTorus d k → Real) : Real :=
  ∑ x : IsingDyadicTorus d k, ∑ i : Fin d,
    (u x - u (x + isingTorusStep i)) *
      (v x - v (x + isingTorusStep i))


noncomputable def isingTorusDirichlet
    (u : IsingDyadicTorus d k → Real) : Real :=
  isingTorusDirichletBilinear u u


def isingTorusSpinField
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    IsingDyadicTorus d k → Real :=
  fun x => spin sigma x


noncomputable def isingTorusShiftedPartition
    (beta : Real) (h : IsingDyadicTorus d k → Real) : Real :=
  ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
    Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma + h))

end StatMech.FrontierA
