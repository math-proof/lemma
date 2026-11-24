module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
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


noncomputable def toIsing (σ : V → Fin 2) : ConfigSpace V := fun x => finTwoEquiv (σ x)

end IsingFK
end StatMech
