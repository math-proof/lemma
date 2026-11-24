module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.IsingFK.Q2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace IsingFK

open Potts Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def betaOfP (p : ℝ) : ℝ := -(1 / 2) * Real.log (1 - p)


noncomputable def pOfBeta (β : ℝ) : ℝ := 1 - Real.exp (-2 * β)


end IsingFK
end StatMech
