/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamDiagonalAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

def grahamLooplessEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter (fun e => ¬ e.IsDiag)

def grahamDiagonalEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter Sym2.IsDiag

end StatMech.FrontierA
