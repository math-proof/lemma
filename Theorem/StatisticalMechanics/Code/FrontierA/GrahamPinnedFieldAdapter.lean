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
import Def.StatisticalMechanics.Code.FrontierA.GrahamPinnedFieldAdapter
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamAnchorCoupling_nonneg (J : Sym2 V -> Real) (m : V)
    (hJ : forall e, 0 <= J e) :
    forall e, 0 <= grahamAnchorCoupling J m e := by
  intro e
  simp only [grahamAnchorCoupling]
  split <;> simp [hJ]

theorem grahamAnchorField_nonneg (E : Finset (Sym2 V))
    (J : Sym2 V -> Real) (m : V) (hJ : forall e, 0 <= J e) :
    forall x, 0 <= grahamAnchorField E J m x := by
  intro x
  by_cases hxm : x = m
  · simp [grahamAnchorField, hxm]
  · by_cases hE : s(x, m) ∈ E
    · simp [grahamAnchorField, hxm, hE, hJ]
    · simp [grahamAnchorField, hxm, hE]


end StatMech.FrontierA
