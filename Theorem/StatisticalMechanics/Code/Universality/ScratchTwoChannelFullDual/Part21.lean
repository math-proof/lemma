/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelFullDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute.Part22
import Theorem.StatisticalMechanics.Code.FK.IndexedBoundaryCondition.Part7
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelFullDual.Part25
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

@[simp] theorem rlc_twoChannelIndexedFaceTag_eq_true_iff {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    rlc_twoChannelIndexedFaceTag gamma gamma' x = true ↔
      RlcTwoChannelIndexedIsFace gamma gamma' x := by
  rcases x with x | (x | x) <;>
    simp [rlc_twoChannelIndexedFaceTag, RlcTwoChannelIndexedIsFace]

@[simp] theorem rlc_twoChannelIndexedFaceTag_outerEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    (rlc_twoChannelIndexedOuterEdge gamma gamma' f).map
        (rlc_twoChannelIndexedFaceTag gamma gamma') = s(false, false) := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hret
    induction hret.choose.1 using Sym2.inductionOn with
    | _ x y =>
        simp [rlc_twoChannelIndexedOuterTarget,
          rlc_twoChannelIndexedFaceTag]
  · simp [rlc_twoChannelIndexedOuterPort,
      rlc_twoChannelIndexedFaceTag]

theorem rlc_twoChannelIndexedSpoke_faceTag_ne_false {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {x y : RlcTwoChannelIndexedOuterVertex gamma gamma'}
    (hxy : (rlc_twoChannelIndexedSpokeGraph gamma gamma').Adj x y) :
    s(x, y).map (rlc_twoChannelIndexedFaceTag gamma gamma') ≠
      s(false, false) := by
  intro htag
  rw [Sym2.map_mk, Sym2.eq_iff] at htag
  have hxfalse : rlc_twoChannelIndexedFaceTag gamma gamma' x = false := by
    rcases htag with htag | htag <;> exact htag.1
  have hyfalse : rlc_twoChannelIndexedFaceTag gamma gamma' y = false := by
    rcases htag with htag | htag <;> exact htag.2
  rcases hxy.2.2 with hx | hy
  · have hxtrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' x).2 hx
    simp [hxtrue] at hxfalse
  · have hytrue := (rlc_twoChannelIndexedFaceTag_eq_true_iff
      gamma gamma' y).2 hy
    simp [hytrue] at hyfalse

theorem rlc_twoChannelIndexedOuterEdge_not_mem_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∉
      (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet := by
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      intro hspoke
      apply rlc_twoChannelIndexedSpoke_faceTag_ne_false gamma gamma' hspoke
      rw [← hxy]
      exact rlc_twoChannelIndexedFaceTag_outerEdge gamma gamma' f


theorem rlc_twoChannelIndexedOuterConfig_spoke {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {e : Sym2 (RlcTwoChannelIndexedOuterVertex gamma gamma')}
    (he : e ∈ (rlc_twoChannelIndexedSpokeGraph gamma gamma').edgeSet) :
    rlc_twoChannelIndexedOuterConfig gamma gamma' omega e = true := by
  unfold rlc_twoChannelIndexedOuterConfig
  split
  · rename_i hrandom
    obtain ⟨f, rfl⟩ := hrandom
    exact (rlc_twoChannelIndexedOuterEdge_not_mem_spoke
      gamma gamma' f he).elim
  · simp [he]

theorem rlc_twoChannelIndexedOuterEdge_ne_diag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma'))
    (x : RlcTwoChannelIndexedOuterVertex gamma gamma') :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ≠ s(x, x) := by
  unfold rlc_twoChannelIndexedOuterEdge
  split
  · rename_i hf
    have hedge := hf.choose.2
    revert hedge
    induction hf.choose.1 using Sym2.inductionOn with
    | _ u v =>
        intro hedge heq
        rw [SimpleGraph.mem_edgeSet] at hedge
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with h | h
        · apply hedge.ne
          exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma'
            (h.1.trans h.2.symm)
        · apply hedge.ne
          exact rlc_twoChannelIndexedOuterTarget_injective gamma gamma'
            (h.2.trans h.1.symm).symm
  · intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · have hbool : false = true := congrArg
          (fun z => match z with
            | Sum.inr (Sum.inl (_, side)) => side
            | _ => false) (h.1.trans h.2.symm)
      simp at hbool
    · have hbool : false = true := congrArg
          (fun z => match z with
            | Sum.inr (Sum.inl (_, side)) => side
            | _ => false) (h.1.trans h.2.symm)
      simp at hbool

theorem rlc_twoChannelIndexedOuterEdge_mem_random {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma')) :
    rlc_twoChannelIndexedOuterEdge gamma gamma' f ∈
      (rlc_twoChannelIndexedRandomGraph gamma gamma').edgeSet := by
  induction hxy : rlc_twoChannelIndexedOuterEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, f, hxy⟩
      intro h
      subst y
      exact rlc_twoChannelIndexedOuterEdge_ne_diag gamma gamma' f x hxy


end
end StatMech.Universality
