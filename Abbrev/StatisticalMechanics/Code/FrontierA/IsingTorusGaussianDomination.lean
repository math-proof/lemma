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
open Finset Filter Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising


abbrev IsingDyadicTorus (d k : Nat) := Fin d → ZMod (2 ^ (k + 2))

end StatMech.FrontierA
