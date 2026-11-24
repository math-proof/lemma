module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexDefectState (n D : Nat) :=
  {d : Fin n → Nat // ∑ i, d i = D}


def sixVertexDefectLowerGraph (n D : Nat) :
    SimpleGraph (SixVertexDefectState n D) where
  Adj d e := SixVertexDefectLowerStep d.1 e.1 ∨
    SixVertexDefectLowerStep e.1 d.1
  symm := by
    constructor
    intro d e h
    exact h.symm
  loopless := by
    refine ⟨?_⟩
    intro d h
    rcases h with h | h
    · have hw := h.weight_add_one
      omega
    · have hw := h.weight_add_one
      omega

end
end StatMech.FrontierD
