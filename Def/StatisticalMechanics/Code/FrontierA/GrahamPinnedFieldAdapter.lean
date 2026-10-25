/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedFieldAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamHeadlineAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGraphAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGTriangle
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamAnchorCoupling (J : Sym2 V -> Real) (m : V) (e : Sym2 V) : Real :=
  if m ∈ e then 0 else J e


def grahamAnchorField (E : Finset (Sym2 V)) (J : Sym2 V -> Real)
    (m x : V) : Real :=
  if x = m then 0 else if s(x, m) ∈ E then J s(x, m) else 0

end StatMech.FrontierA
