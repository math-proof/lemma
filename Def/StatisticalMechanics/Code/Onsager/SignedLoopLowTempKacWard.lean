/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Abbrev.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

def kwg_subdivLeftEdge (ends : E -> Sym2 V) (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inl (ends e).out.1, Sum.inr (e, false))


def kwg_subdivCentralEdge (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inr (e, false), Sum.inr (e, true))


def kwg_subdivRightEdge (ends : E -> Sym2 V) (e : E) : kwg_SubdivEdge V E :=
  s(Sum.inr (e, true), Sum.inl (ends e).out.2)


def kwg_subdivGadgetEdges (ends : E -> Sym2 V) (e : E) :
    Finset (kwg_SubdivEdge V E) :=
  {kwg_subdivLeftEdge ends e, kwg_subdivCentralEdge e,
    kwg_subdivRightEdge ends e}


def kwg_subdivLift (ends : E -> Sym2 V) (F : Finset E) :
    Finset (kwg_SubdivEdge V E) :=
  F.biUnion (kwg_subdivGadgetEdges ends)


def kwg_subdivWeight (x : E -> ℂ) : kwg_SubdivEdge V E -> ℂ :=
  fun edge => if h : ∃ e : E, kwg_subdivCentralEdge e = edge
    then x h.choose else 1

end
end StatMech.Onsager
