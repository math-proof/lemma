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
import Def.StatisticalMechanics.Code.Onsager.SignedLoopPlusRectCutCycle.Part4
open Finset SimpleGraph
open scoped symmDiff


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.FrontierA StatMech.Walls

noncomputable section

theorem ons_plusRectContour_isEven (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    IsEvenSubgraph (ons_plusRectContour n tau) :=
  isEvenSubgraph_transportEdges (ons_plusDualFaceEquivRect n)
    (ons_plusDualContourFace_isEven n tau)

theorem ons_touchingBondToRectEdge_eq_transport (n : Nat)
    (edge : ons_PlusWiredBond 2 n) :
    ons_touchingBondToRectEdge n edge =
      Sym2.map (ons_plusDualFaceEquivRect n)
        (ons_plusDualFaceEdgeLift n
          (ons_touchingBondEquivPlusDualEdge n edge)) := by
  rfl


theorem ons_plusRectDualCut_optionAnchoredEquiv (n : Nat)
    (tau : {x // x ∈ box 2 n} -> Bool) :
    ons_plusRectDualCut n (ons_optionAnchoredEquiv tau) =
      ons_plusRectContour n tau := by
  ext rectEdge
  constructor
  · intro hrect
    rw [ons_plusRectDualCut, Finset.mem_map] at hrect
    obtain ⟨typed, htyped, rfl⟩ := hrect
    have hprimal := (mem_plusWiredCut_iff 2 n tau typed).mp htyped
    have hdual : flankFacesSym typed.1 ∈ ons_plusDualContour n tau := by
      rw [ons_plusDualContour, Finset.mem_image]
      exact ⟨typed.1, hprimal, rfl⟩
    let source : {edge // edge ∈ ons_plusDualContour n tau} :=
      ⟨flankFacesSym typed.1, hdual⟩
    let supported : {edge // edge ∈ ons_plusDualFaceEdgeSet n} :=
      ons_touchingBondEquivPlusDualEdge n typed
    have hsupported : supported.1 = source.1 := rfl
    rw [ons_plusRectContour, transportEdges, Finset.mem_image]
    refine ⟨ons_plusDualFaceEdgeLift n supported, ?_, ?_⟩
    · rw [ons_plusDualContourFace, Finset.mem_map]
      refine ⟨source, Finset.mem_attach _ _, ?_⟩
      exact congrArg (ons_plusDualFaceEdgeLift n) (Subtype.ext hsupported.symm)
    · exact (ons_touchingBondToRectEdge_eq_transport n typed).symm
  · intro hrect
    rw [ons_plusRectContour, transportEdges, Finset.mem_image] at hrect
    obtain ⟨faceEdge, hface, hrectEq⟩ := hrect
    rw [ons_plusDualContourFace, Finset.mem_map] at hface
    obtain ⟨source, _, hsource⟩ := hface
    have hsourceContour : source.1 ∈ ons_plusDualContour n tau := source.2
    unfold ons_plusDualContour at hsourceContour
    rw [Finset.mem_image] at hsourceContour
    obtain ⟨primalEdge, hprimal, hprimalDual⟩ := hsourceContour
    have hbond : primalEdge ∈ bondFinsetTouch 2 n :=
      (Finset.mem_filter.mp hprimal).1
    let typed : ons_PlusWiredBond 2 n := ⟨primalEdge, hbond⟩
    have htyped : typed ∈ multibondCut (ons_plusWiredBondEnds 2 n)
        (ons_optionAnchoredEquiv tau).1 :=
      (mem_plusWiredCut_iff 2 n tau typed).mpr hprimal
    rw [ons_plusRectDualCut, Finset.mem_map]
    refine ⟨typed, htyped, ?_⟩
    change ons_touchingBondToRectEdge n typed = rectEdge
    rw [ons_touchingBondToRectEdge_eq_transport]
    calc
      Sym2.map (ons_plusDualFaceEquivRect n)
          (ons_plusDualFaceEdgeLift n
            (ons_touchingBondEquivPlusDualEdge n typed)) =
          Sym2.map (ons_plusDualFaceEquivRect n) faceEdge := by
            congr 1
            rw [← hsource]
            apply congrArg (ons_plusDualFaceEdgeLift n)
            apply Subtype.ext
            exact hprimalDual
      _ = rectEdge := hrectEq

theorem ons_plusRectDualCut_isEven (n : Nat)
    (config : AnchoredConfig (ons_PlusWiredVertex 2 n) none) :
    IsEvenSubgraph (ons_plusRectDualCut n config) := by
  let tau := (ons_optionAnchoredEquiv
    (I := {x // x ∈ box 2 n})).symm config
  rw [show config = ons_optionAnchoredEquiv tau by
    exact ((ons_optionAnchoredEquiv
      (I := {x // x ∈ box 2 n})).apply_symm_apply config).symm,
    ons_plusRectDualCut_optionAnchoredEquiv]
  exact ons_plusRectContour_isEven n tau

theorem ons_multibondSupportGraph_plusWired_adj_some
    (n : Nat) (x y : {z // z ∈ box 2 n})
    (hxy : (StatMech.FK.boxGraph 2 n).Adj x y) :
    (ons_multibondSupportGraph (ons_plusWiredBondEnds 2 n)).Adj
      (some x) (some y) := by
  have hlat : (hypercubicLattice 2).Adj x.1 y.1 :=
    (SimpleGraph.comap_adj.mp hxy)
  have hbond : s(x.1, y.1) ∈ bondFinsetTouch 2 n :=
    mk_mem_bondFinsetTouch hlat (Or.inl x.2)
  let edge : ons_PlusWiredBond 2 n := ⟨s(x.1, y.1), hbond⟩
  refine ⟨fun h => hlat.ne (congrArg Subtype.val (Option.some.inj h)), edge, ?_⟩
  have hout : s(edge.1.out.1, edge.1.out.2) = s(x.1, y.1) := by
    exact edge.1.out_eq.trans rfl
  rw [Sym2.eq_iff] at hout
  rcases hout with hout | hout
  · left
    simp [ons_plusWiredBondEnds, ons_plusWiredVertexOfSite,
      hout.1, hout.2, x.2, y.2]
  · right
    simp [ons_plusWiredBondEnds, ons_plusWiredVertexOfSite,
      hout.1, hout.2, x.2, y.2]


end
end StatMech.Onsager
