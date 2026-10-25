/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusRectCutCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualRectangle.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWDualBijection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.BoxGraphPath.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part5
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_plusWiredEastSite_mem_box (n : Nat) :
    ons_plusWiredEastSite n ∈ box 2 n := by
  intro i
  fin_cases i <;> simp [ons_plusWiredEastSite]

theorem ons_plusWiredEastOutsideSite_not_mem_box (n : Nat) :
    ons_plusWiredEastOutsideSite n ∉ box 2 n := by
  intro h
  have h0 := h 0
  simp [ons_plusWiredEastOutsideSite] at h0
  rw [show (↑n : Int) + 1 = (↑(n + 1) : Int) by omega] at h0
  norm_num at h0
  omega

theorem ons_plusWiredEast_adj (n : Nat) :
    (hypercubicLattice 2).Adj
      (ons_plusWiredEastSite n) (ons_plusWiredEastOutsideSite n) := by
  exact latAdj_right (n : Int) 0

theorem ons_multibondSupportGraph_plusWired_root_adj (n : Nat) :
    (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
      none (some ⟨ons_plusWiredEastSite n,
        ons_plusWiredEastSite_mem_box n⟩) := by
  let x : {z // z ∈ box 2 n} :=
    ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩
  let y := ons_plusWiredEastOutsideSite n
  change (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
    none (some x)
  have hlat : (hypercubicLattice 2).Adj x.1 y := ons_plusWiredEast_adj n
  have hbond : s(x.1, y) ∈ bondFinsetTouch 2 n :=
    mk_mem_bondFinsetTouch hlat (Or.inl x.2)
  let edge : ons_PlusWiredBond 2 n := ⟨s(x.1, y), hbond⟩
  refine ⟨by simp, edge, ?_⟩
  have hout : s(edge.1.out.1, edge.1.out.2) = s(x.1, y) := by
    exact edge.1.out_eq.trans rfl
  rw [Sym2.eq_iff] at hout
  have hxmap : ons_plusWiredVertexOfSite 2 n x.1 = some x := by
    simp [ons_plusWiredVertexOfSite, x.2]
  have hy : y ∉ box 2 n := ons_plusWiredEastOutsideSite_not_mem_box n
  have hymap : ons_plusWiredVertexOfSite 2 n y = none := by
    simp [ons_plusWiredVertexOfSite, hy]
  rcases hout with hout | hout
  · right
    simp only [ons_plusWiredBondEnds, hout.1, hout.2, hxmap, hymap]
  · left
    simp only [ons_plusWiredBondEnds, hout.1, hout.2, hxmap, hymap]

theorem ons_multibondSupportGraph_plusWired_connected (n : Nat) :
    (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Connected := by
  constructor
  intro v w
  have hv : (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Reachable v none := by
    cases v with
    | none => exact ⟨.nil⟩
    | some x =>
        apply Reachable.symm
        apply (ons_multibondSupportGraph_plusWired_root_adj n).reachable.trans
        change (ons_multibondSupportGraph
          (ons_plusWiredBondEnds 2 n)).Reachable
            (some ⟨ons_plusWiredEastSite n,
              ons_plusWiredEastSite_mem_box n⟩) (some x)
        exact (StatMech.FrontierB.boxGraph_preconnected 2 n
          ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩ x).map
            (ons_boxToPlusWiredSupportHom n)
  have hw : (ons_multibondSupportGraph
      (ons_plusWiredBondEnds 2 n)).Reachable none w := by
    cases w with
    | none => exact ⟨.nil⟩
    | some x =>
        apply (ons_multibondSupportGraph_plusWired_root_adj n).reachable.trans
        change (ons_multibondSupportGraph
          (ons_plusWiredBondEnds 2 n)).Reachable
            (some ⟨ons_plusWiredEastSite n,
              ons_plusWiredEastSite_mem_box n⟩) (some x)
        exact (StatMech.FrontierB.boxGraph_preconnected 2 n
          ⟨ons_plusWiredEastSite n, ons_plusWiredEastSite_mem_box n⟩ x).map
            (ons_boxToPlusWiredSupportHom n)
  exact hv.trans hw

theorem ons_plusRectDualCut_injective (n : Nat) :
    Function.Injective (ons_plusRectDualCut n) := by
  intro config config' h
  apply multibondCut_anchored_injective_of_connected
    (ons_plusWiredBondEnds 2 n) none
    (ons_multibondSupportGraph_plusWired_connected n)
  apply Finset.map_injective
    ⟨ons_touchingBondToRectEdge n, ons_touchingBondToRectEdge_injective n⟩
  exact h


end
end StatMech.Onsager
