module
public import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
public import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
public import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
public import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
open scoped BigOperators
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.Ising StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_lowTempPathSign (config : ConfigSpace V)
    {u v : V} (path : G.Walk u v) : Real :=
  if Even (kwd_crossCount (kwd_sideBoundary config) path) then 1 else -1


end StatMech.Onsager
