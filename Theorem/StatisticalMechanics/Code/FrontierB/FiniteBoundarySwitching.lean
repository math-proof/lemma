/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
import Def.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sourceToggle_inter_eq_iff
    (interior U A : Finset V) (hU : U ⊆ interior) :
    (A ∆ U) ∩ interior = U ↔ A ∩ interior = ∅ := by
  constructor
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    have hxU : x ∈ U → x ∈ interior := fun hxU => hU hxU
    simp only [Finset.mem_inter, Finset.mem_symmDiff,
      Finset.notMem_empty] at hx ⊢
    tauto
  · intro h
    ext x
    have hx := Finset.ext_iff.mp h x
    have hxU : x ∈ U → x ∈ interior := fun hxU => hU hxU
    simp only [Finset.mem_inter, Finset.mem_symmDiff,
      Finset.notMem_empty] at hx ⊢
    tauto


end StatMech.FrontierB
