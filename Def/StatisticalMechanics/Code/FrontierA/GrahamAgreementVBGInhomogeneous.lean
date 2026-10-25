/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBGInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamAgreementVBG
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Sharpness

open StatMech.Walls StatMech.Walls.VBG

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def grahamInhomOne (K : Sym2 V -> Real) (hf : V -> Real)
    (x : V) : Real :=
  expJ G.edgeFinset K hf (fun s => spin s x)


end StatMech.FrontierA
