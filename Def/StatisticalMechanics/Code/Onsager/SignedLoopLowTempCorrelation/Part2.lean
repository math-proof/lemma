/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_lowTempPathNumerator (beta : Real)
    {u v : V} (path : G.Walk u v) : Real :=
  ∑ config : ConfigSpace V,
    ons_lowTempPathSign G config path *
      Real.exp (-2 * beta) ^ (cutEdges G config).card


noncomputable def ons_lowTempContourDenominator (beta : Real) : Real :=
  ∑ config : ConfigSpace V,
    Real.exp (-2 * beta) ^ (cutEdges G config).card


end StatMech.Onsager
