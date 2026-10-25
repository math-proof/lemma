/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamPinnedVBGMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGCore
open Finset
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.ConfigSpace

open StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def grahamPinnedProb
    (E : Finset (Sym2 V)) (J : Sym2 V -> Real) (m : V) :
    ConfigSpace V -> Real :=
  vbg_condPlus (grahamZeroProb E J) (vbg_coordUp m)


end StatMech.FrontierA
