/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorProfileCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy


section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

theorem graham_disjoint_fiberwise
    (S T : Finset (Sigma fun e : E => gamma e)) :
    Disjoint S T <->
      forall e, Disjoint (sigmaFinsetEquivPi S e)
        (sigmaFinsetEquivPi T e) := by
  constructor
  · intro h e
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rw [graham_mem_sigmaFinsetEquivPi] at hxS hxT
    exact (Finset.disjoint_left.mp h) hxS hxT
  · intro h
    rw [Finset.disjoint_left]
    rintro ⟨e, x⟩ hxS hxT
    have hxs : x ∈ sigmaFinsetEquivPi S e := by
      rw [graham_mem_sigmaFinsetEquivPi]
      exact hxS
    have hxt : x ∈ sigmaFinsetEquivPi T e := by
      rw [graham_mem_sigmaFinsetEquivPi]
      exact hxT
    exact (Finset.disjoint_left.mp (h e)) hxs hxt

theorem grahamFourColor_partition_fiberwise
    (c : GrahamFourColoring (Sigma fun e : E => gamma e)) :
    c.IsPartition Finset.univ <->
      forall e, (grahamFourColorSigmaEquivPi c e).IsPartition Finset.univ := by
  simp only [GrahamFourColoring.IsPartition, subset_univ, true_and]
  rw [graham_disjoint_fiberwise, graham_disjoint_fiberwise,
    graham_disjoint_fiberwise]
  constructor
  · rintro ⟨h12, h13, h23⟩ e
    exact ⟨h12 e, h13 e, h23 e⟩
  · intro h
    exact ⟨fun e => (h e).1, fun e => (h e).2.1,
      fun e => (h e).2.2⟩


end SigmaPi
end StatMech.FrontierA
