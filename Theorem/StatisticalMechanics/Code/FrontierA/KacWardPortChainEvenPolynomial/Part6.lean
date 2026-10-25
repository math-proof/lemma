/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part6
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwDartOfPort_matchingNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : KWDartPort G) :
    kwDartOfPort G (kwOrderedMatchingNeighbor G p) =
      (kwDartOfPort G p).symm := by
  simp [kwOrderedMatchingNeighbor]

theorem kwOrderedMatchingNeighbor_not_mem_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    kwOrderedMatchingNeighbor G p ∉
      kwOrderedInternalNeighborFinset G order p := by
  intro hmem
  rw [mem_kwOrderedInternalNeighborFinset] at hmem
  have hfirst : (kwDartOfPort G p).snd =
      (kwOrderedMatchingNeighbor G p).1 := by
    simpa using kwDartOfPort_fst G (kwOrderedMatchingNeighbor G p)
  apply (kwDartOfPort G p).fst_ne_snd
  calc
    (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
    _ = (kwOrderedMatchingNeighbor G p).1 := hmem.1
    _ = (kwDartOfPort G p).snd := hfirst.symm

theorem kwOrderedSplit_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G order).neighborFinset p =
      insert (kwOrderedMatchingNeighbor G p)
        (kwOrderedInternalNeighborFinset G order p) := by
  ext q
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    mem_kwOrderedInternalNeighborFinset,
    kwOrderedDartPortSplitGraph_adj]
  constructor
  · rintro (hext | hint)
    · left
      apply kwDartOfPort_injective G
      rw [hext]
      simp
    · exact Or.inr hint
  · rintro (rfl | hint)
    · left
      simp
    · exact Or.inr hint


end StatMech.FrontierA
