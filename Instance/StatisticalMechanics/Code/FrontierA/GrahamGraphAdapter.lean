/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGraphAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Def.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


instance grahamGraph_decidableAdj (E : Finset (Sym2 V)) :
    DecidableRel (grahamGraph E).Adj := by
  intro x y
  unfold grahamGraph
  infer_instance


end StatMech.FrontierA
