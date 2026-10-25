/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part55
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorFaceBox_faceFlipX_iff (n : Int) (f : Site 2) :
    f ∈ rlc_connectorFaceBox n ↔
      rlc_faceFlipX f ∈ rlc_connectorFaceBox n := by
  simp only [rlc_connectorFaceBox, Set.Finite.mem_toFinset, mem_rect,
    rlc_faceFlipX, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega


theorem rlc_connectorFourTraceEdges_flipX_iff
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) (e : Sym2 (Site 2)) :
    e ∈ rlc_connectorFourTraceEdges gamma gamma' ↔
      Sym2.map rlc_flipX e ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
  have forward (d : Sym2 (Site 2))
      (hd : d ∈ rlc_connectorFourTraceEdges gamma gamma') :
      Sym2.map rlc_flipX d ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
    rw [rlc_connectorFourTraceEdges,
      rlc_connectorReflectedTraceEdges] at hd ⊢
    rcases Finset.mem_union.mp hd with horiginal | hreflected
    · rcases Finset.mem_union.mp horiginal with hright | hleft
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨d, hright, rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨d, hleft, rfl⟩))
    · rcases Finset.mem_union.mp hreflected with hright | hleft
      · obtain ⟨e₀, he₀, heq⟩ := Finset.mem_image.mp hright
        apply Finset.mem_union_left _
        apply Finset.mem_union_left _
        have hmap : Sym2.map rlc_flipX d = e₀ := by
          rw [← heq, Sym2.map_map]
          simpa [Function.comp_def]
        rwa [hmap]
      · obtain ⟨e₀, he₀, heq⟩ := Finset.mem_image.mp hleft
        apply Finset.mem_union_left _
        apply Finset.mem_union_right _
        have hmap : Sym2.map rlc_flipX d = e₀ := by
          rw [← heq, Sym2.map_map]
          simpa [Function.comp_def]
        rwa [hmap]
  constructor
  · exact forward e
  · intro he
    have h := forward (Sym2.map rlc_flipX e) he
    simpa [Sym2.map_map, Function.comp_def] using h


theorem rlc_sharedPrimalEdge_faceFlipX
    {f g : Site 2} (hfg : (hypercubicLattice 2).Adj f g) :
    sharedPrimalEdge (rlc_faceFlipX f) (rlc_faceFlipX g) =
      Sym2.map rlc_flipX (sharedPrimalEdge f g) := by
  rcases face_adj_dir hfg with hg | hg | hg | hg <;> subst g <;>
    simp [rlc_faceFlipX, sharedPrimalEdge, Sym2.map_mk,
      rlc_flipX, rlc_flipXFun, faceCorner00, faceCorner01,
      faceCorner10, faceCorner11, Sym2.eq_swap] <;> omega


theorem rlc_flankFaces_flipX
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b) :
    flankFaces (rlc_flipX a) (rlc_flipX b) =
      Sym2.map rlc_faceFlipX (flankFaces a b) := by
  rcases face_adj_dir hab with hb | hb | hb | hb <;> subst b <;>
    simp [rlc_faceFlipX, flankFaces, Sym2.map_mk,
      rlc_flipX, rlc_flipXFun, faceCorner00, faceCorner01,
      faceCorner10, faceCorner11, Sym2.eq_swap] <;> omega


theorem RlcBookFaithfulTracePair.centralFaceRegion_faceFlipX
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {f : Site 2}
    (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma') :
    rlc_faceFlipX f ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
  have hfSet : f ∈
      rlc_connectorCentralFaceRegionSet gamma gamma' := by
    simpa [rlc_connectorCentralFaceRegion] using hf
  obtain ⟨hfBox, hcentralBox, hreach⟩ := hfSet
  let hom : rlc_connectorFiniteFaceCutGraph gamma gamma' →g
      rlc_connectorFiniteFaceCutGraph gamma gamma' := {
    toFun := fun z ↦
      ⟨rlc_faceFlipX z.1,
        (rlc_connectorFaceBox_faceFlipX_iff n z.1).mp z.2⟩
    map_rel' := by
      intro a b hab
      have hab0 : (rlc_connectorFourTraceFaceCutGraph
          gamma gamma').Adj a.1 b.1 := hab
      change (rlc_connectorFourTraceFaceCutGraph gamma gamma').Adj
        (rlc_faceFlipX a.1) (rlc_faceFlipX b.1)
      rw [rlc_connectorFourTraceFaceCutGraph_adj] at hab0 ⊢
      refine ⟨rlc_faceFlipXLatticeHom.map_rel hab0.1, ?_⟩
      intro hwall
      rw [rlc_sharedPrimalEdge_faceFlipX hab0.1] at hwall
      exact hab0.2
        ((rlc_connectorFourTraceEdges_flipX_iff gamma gamma'
          (sharedPrimalEdge a.1 b.1)).2 hwall) }
  have hreachFlip := hreach.map hom
  have hseed : (![-1, 0] : Site 2) ∈
      rlc_connectorCentralFaceRegion gamma gamma' := by
    apply rlc_axisGapFace_mem_connectorCentralFaceRegion
      gamma gamma' hfaith
    · exact le_of_lt hfaith.right_axis_strict
    · exact hfaith.left_axis_strict
  have hseedBox : (![-1, 0] : Site 2) ∈
      rlc_connectorFaceBox n := by
    simp [rlc_connectorFaceBox, mem_rect]
    have hn := hfaith.scale_pos
    omega
  have htargetBox : rlc_faceFlipX f ∈
      rlc_connectorFaceBox n :=
    (rlc_connectorFaceBox_faceFlipX_iff n f).mp hfBox
  have hreach' : (rlc_connectorFiniteFaceCutGraph gamma gamma').Reachable
      ⟨(![-1, 0] : Site 2), hseedBox⟩
      ⟨rlc_faceFlipX f, htargetBox⟩ := by
    simpa [hom, rlc_connectorCentralFace, rlc_faceFlipX] using hreachFlip
  exact rlc_connectorCentralFaceRegion_of_cut_reachable
    gamma gamma' hseed hseedBox htargetBox hreach'


theorem RlcBookFaithfulTracePair.centralFacePlanarEdges_flipX
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b)
    (he : s(a, b) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma') :
    s(rlc_flipX a, rlc_flipX b) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at he ⊢
  rcases he with hclosure | hwall
  · left
    rw [rlc_mem_connectorCentralFaceClosureEdges_iff gamma gamma' hab]
      at hclosure
    have hflipAdj : (hypercubicLattice 2).Adj
        (rlc_flipX a) (rlc_flipX b) :=
      rlc_flipXLatticeHom.map_rel hab
    rw [rlc_mem_connectorCentralFaceClosureEdges_iff
      gamma gamma' hflipAdj]
    rcases hclosure with ⟨haBox, hbBox, f, hfRegion, hfFlank⟩
    refine ⟨(rlc_connectorBox_mem_flipX_iff a).mp haBox,
      (rlc_connectorBox_mem_flipX_iff b).mp hbBox,
      rlc_faceFlipX f,
      hfaith.centralFaceRegion_faceFlipX hfRegion, ?_⟩
    rw [rlc_flankFaces_flipX hab]
    induction hflank : flankFaces a b using Sym2.inductionOn with
    | _ u v =>
        rw [hflank, Sym2.mem_iff] at hfFlank
        simp only [Sym2.map_mk]
        rw [Sym2.mem_iff]
        rcases hfFlank with rfl | rfl <;> simp
  · right
    have hmap := (rlc_connectorFourTraceEdges_flipX_iff
      gamma gamma' s(a, b)).1 hwall
    simpa [Sym2.map_mk] using hmap


theorem rlc_flipXEdge_target_or_originalTrace_or_notPlanar
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b) :
    (∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet,
      target.1.map Subtype.val =
        s(rlc_flipX a, rlc_flipX b)) ∨
      s(rlc_flipX a, rlc_flipX b) ∈
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
      s(rlc_flipX a, rlc_flipX b) ∉
        rlc_connectorCentralFacePlanarEdges gamma gamma' := by
  by_cases hplanar : s(rlc_flipX a, rlc_flipX b) ∈
      rlc_connectorCentralFacePlanarEdges gamma gamma'
  · have haBox : rlc_flipX a ∈
        rect (-2 * n) (2 * n) (-n) n := by
      simpa [rlc_connectorBox] using
        (rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (Sym2.mem_mk_left _ _))
    have hbBox : rlc_flipX b ∈
        rect (-2 * n) (2 * n) (-n) n := by
      simpa [rlc_connectorBox] using
        (rlc_connectorCentralFacePlanarEdge_endpoints_mem_box
          gamma gamma' hplanar (Sym2.mem_mk_right _ _))
    let af : RlcConnectorVertex n := ⟨rlc_flipX a, haBox⟩
    let bf : RlcConnectorVertex n := ⟨rlc_flipX b, hbBox⟩
    have hflipAdj : (hypercubicLattice 2).Adj
        (rlc_flipX a) (rlc_flipX b) :=
      rlc_flipXLatticeHom.map_rel hab
    have hclosure : (rlc_connectorCentralFaceClosureGraph
        gamma gamma').Adj af bf := by
      exact ⟨hflipAdj, by simpa [af, bf] using hplanar⟩
    rw [rlc_connectorCentralFaceClosureGraph_eq_twoChannel_sup_trace]
      at hclosure
    rcases hclosure with htwo | htrace
    · left
      let target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet :=
        ⟨s(af, bf), (SimpleGraph.mem_edgeSet _).mpr htwo⟩
      exact ⟨target, by simp [target, af, bf, Sym2.map_mk]⟩
    · right; left
      simpa [af, bf] using htrace.2
  · exact Or.inr (Or.inr hplanar)


theorem rlc_originalTraceEdge_not_crosses_liftVertexCut
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (B : Set (RlcConnectorVertex n))
    (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
    (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
    {a b : Site 2}
    (htrace : s(a, b) ∈ rlc_pathEdges gamma.1 ∪
      rlc_pathEdges gamma'.1) :
    ¬rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B) s(a, b) := by
  have habSame :
      a ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔
        b ∈ rlc_twoChannelFullPhysicalLiftVertexCut B := by
    rw [Finset.mem_union] at htrace
    rcases htrace with hright | hleft
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma.1 hright
      have haBox := rlc_rightPathVertex_mem_connectorBox gamma hends.1
      have hbBox := rlc_rightPathVertex_mem_connectorBox gamma hends.2
      have haB : a ∈ rlc_twoChannelFullPhysicalLiftVertexCut B :=
        ⟨haBox, hBright ⟨a, haBox⟩ hends.1⟩
      have hbB : b ∈ rlc_twoChannelFullPhysicalLiftVertexCut B :=
        ⟨hbBox, hBright ⟨b, hbBox⟩ hends.2⟩
      exact iff_of_true haB hbB
    · have hends := rlc_pathEdge_endpoints_mem_vertices gamma'.1 hleft
      have haNot : a ∉ rlc_twoChannelFullPhysicalLiftVertexCut B := by
        rintro ⟨haBox, haB⟩
        exact hBleft ⟨a, haBox⟩ hends.1 haB
      have hbNot : b ∉ rlc_twoChannelFullPhysicalLiftVertexCut B := by
        rintro ⟨hbBox, hbB⟩
        exact hBleft ⟨b, hbBox⟩ hends.2 hbB
      exact iff_of_false haNot hbNot
  apply (rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic
    (rlc_twoChannelFullPhysicalLiftVertexCut B) s(a, b)).2
  intro u v huv
  rw [Sym2.eq_iff] at huv
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact habSame
  · exact habSame.symm


theorem
    rlc_twoChannelFullPhysical_noPair_rawTarget_sourceMissing_or_notAcrossA
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (A B : Set (RlcConnectorVertex n))
    (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      rlc_twoChannelFullPhysicalEdgeCrossesCut A
          (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧
        rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
    (target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet)
    (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut
      (rlc_twoChannelFullPhysicalLiftVertexCut B)
        (target.1.map Subtype.val)) :
    (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
        (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨
      ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
        physical.1 = target ∧
          ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A
            (rlc_twoChannelFullPhysicalSourceEdge physical).1 := by
  by_cases hsource : Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma'
      (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))
  · right
    let physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' :=
      ⟨target, hsource⟩
    refine ⟨physical, rfl, ?_⟩
    intro hcrossA
    apply hnoPair
    refine ⟨physical, hcrossA, ?_⟩
    exact (rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff
      B physical.1).2 (by simpa [physical] using hcrossB)
  · exact Or.inl hsource


theorem rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint
    {a b : Site 2} (hab : (hypercubicLattice 2).Adj a b) :
    ∃ z ∈ s(a, b),
      z ∈ rlc_pimsEdgeEquiv s(rlc_flipX a, rlc_flipX b) := by
  rcases face_adj_dir hab with hb | hb | hb | hb
  · subst b
    refine ⟨a, Sym2.mem_mk_left _ _, ?_⟩
    have hedge : s(rlc_flipX a, rlc_flipX ![a 0 + 1, a 1]) =
        s(![-a 0 - 1, a 1], ![-a 0, a 1]) := by
      rw [Sym2.eq_iff]
      right
      constructor
      · ext i
        fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
      · ext i
        fin_cases i <;> simp [rlc_flipX, rlc_flipXFun] <;> ring
    rw [hedge]
    rw [show s(![-a 0 - 1, a 1], ![-a 0, a 1]) =
        s(![-a 0 - 1, a 1], ![(-a 0 - 1) + 1, a 1]) by
      rw [Sym2.eq_iff]
      left
      constructor
      · rfl
      · ext i
        fin_cases i <;> simp <;> try ring]
    rw [rlc_pimsEdgeEquiv_horizontal]
    rw [Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp <;> ring
  · subst b
    refine ⟨(![a 0 - 1, a 1] : Site 2), Sym2.mem_mk_right _ _, ?_⟩
    have hedge : s(rlc_flipX a, rlc_flipX ![a 0 - 1, a 1]) =
        s(![-a 0, a 1], ![-a 0 + 1, a 1]) := by
      rw [Sym2.eq_iff]
      left
      constructor <;> ext i <;> fin_cases i <;>
        simp [rlc_flipX, rlc_flipXFun] <;> try ring
    rw [hedge]
    rw [rlc_pimsEdgeEquiv_horizontal]
    rw [Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp <;> ring
  · subst b
    refine ⟨a, Sym2.mem_mk_left _ _, ?_⟩
    have hedge : s(rlc_flipX a, rlc_flipX ![a 0, a 1 + 1]) =
        s(![-a 0, a 1], ![-a 0, a 1 + 1]) := by
      rw [Sym2.eq_iff]
      left
      constructor <;> ext i <;> fin_cases i <;>
        simp [rlc_flipX, rlc_flipXFun] <;> try ring
    rw [hedge]
    rw [rlc_pimsEdgeEquiv_vertical]
    rw [Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp <;> ring
  · subst b
    refine ⟨(![a 0, a 1 - 1] : Site 2), Sym2.mem_mk_right _ _, ?_⟩
    have hedge : s(rlc_flipX a, rlc_flipX ![a 0, a 1 - 1]) =
        s(![-a 0, a 1 - 1], ![-a 0, a 1]) := by
      rw [Sym2.eq_iff]
      right
      constructor
      · ext i
        fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
      · ext i
        fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
    rw [hedge]
    rw [show s(![-a 0, a 1 - 1], ![-a 0, a 1]) =
        s(![-a 0, a 1 - 1], ![-a 0, (a 1 - 1) + 1]) by
      rw [Sym2.eq_iff]
      left
      constructor
      · rfl
      · ext i
        fin_cases i <;> simp <;> try ring]
    rw [rlc_pimsEdgeEquiv_vertical]
    rw [Sym2.mem_iff]
    right
    ext i
    fin_cases i <;> simp <;> try ring


theorem rlc_latticeEdge_threeSupport_cases
    {x y a b c : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hsupport : ∀ z ∈ s(x, y), z = a ∨ z = b ∨ z = c) :
    s(x, y) = s(a, b) ∨ s(x, y) = s(a, c) ∨
      s(x, y) = s(b, c) := by
  have hx := hsupport x (Sym2.mem_mk_left _ _)
  have hy := hsupport y (Sym2.mem_mk_right _ _)
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals try { exact False.elim (hxy.ne rfl) }
  all_goals simp [Sym2.eq_swap]


theorem rlc_doubleDualShift_eq_dualReflect_symm_iff
    (p w : Site 2) :
    phb_doubleDualShift p = rlc_dualReflect.symm w ↔
      p = rlc_flipX w := by
  constructor
  · intro h
    have h0 := congrArg (fun z : Site 2 => z 0) h
    have h1 := congrArg (fun z : Site 2 => z 1) h
    ext i
    fin_cases i <;>
      simp [phb_doubleDualShift, rlc_dualReflect,
        rlc_dualReflectInvFun, rlc_flipX, rlc_flipXFun] at h0 h1 ⊢ <;>
      omega
  · rintro rfl
    exact rlc_doubleDualShift_flipX_eq_dualReflect_symm w


theorem rlc_shiftedReach_ne_dualReflectSymm_of_flippedLeftTrace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p w : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hwLeft : rlc_flipX w ∈ rlc_pathVertices gamma'.1) :
    phb_doubleDualShift p ≠ rlc_dualReflect.symm w := by
  intro h
  have hpEq :=
    (rlc_doubleDualShift_eq_dualReflect_symm_iff p w).1 h
  exact (rlc_leftPathVertex_not_mem_twoChannelFullReachSet_of_failure
    gamma gamma' omega hno hwLeft) (hpEq ▸ hpReach)


theorem rlc_shiftedExterior_ne_dualReflectSymm_of_flippedRightTrace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {q w : Site 2}
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hwRight : rlc_flipX w ∈ rlc_pathVertices gamma.1) :
    phb_doubleDualShift q ≠ rlc_dualReflect.symm w := by
  intro h
  have hqEq :=
    (rlc_doubleDualShift_eq_dualReflect_symm_iff q w).1 h
  apply hqOut
  rw [hqEq]
  exact rlc_twoChannelFullReachSet_subset_filled gamma gamma' omega
    (rlc_rightPathVertex_mem_twoChannelFullReachSet
      gamma gamma' omega hwRight)


theorem rlc_shiftedReach_ne_exclusiveReflectedLeftFace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
      rlc_finiteTwoChannelConnectorEvent gamma gamma')
    {p f : Site 2}
    (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
    (hfLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation
      gamma gamma' (rlc_dualReflect f)) :
    phb_doubleDualShift p ≠ f := by
  have hf : f = rlc_dualReflect.symm (rlc_dualReflect f) := by
    exact (rlc_dualReflect.symm_apply_apply f).symm
  obtain ⟨w, hwLeft, hfw⟩ := hfLeft.2.1
  have hflip : rlc_flipX (rlc_dualReflect f) ∈
      rlc_pathVertices gamma'.1 := by
    rw [hfw]
    simpa using hwLeft
  rw [hf]
  exact rlc_shiftedReach_ne_dualReflectSymm_of_flippedLeftTrace
    hno hpReach hflip


theorem rlc_shiftedExterior_ne_exclusiveReflectedRightFace
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {q f : Site 2}
    (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
    (hfRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation
      gamma gamma' (rlc_dualReflect f)) :
    phb_doubleDualShift q ≠ f := by
  have hf : f = rlc_dualReflect.symm (rlc_dualReflect f) := by
    exact (rlc_dualReflect.symm_apply_apply f).symm
  obtain ⟨w, hwRight, hfw⟩ := hfRight.2.1
  have hflip : rlc_flipX (rlc_dualReflect f) ∈
      rlc_pathVertices gamma.1 := by
    rw [hfw]
    simpa using hwRight
  rw [hf]
  exact rlc_shiftedExterior_ne_dualReflectSymm_of_flippedRightTrace
    hqOut hflip


theorem rlc_shiftedExterior_mem_or_adj_boundaryEdge
    {p q f g : Site 2}
    (hpq : (hypercubicLattice 2).Adj p q)
    (hinc : phb_doubleDualShift p ∈ s(f, g) ∨
      phb_doubleDualShift q ∈ s(f, g)) :
    phb_doubleDualShift q ∈ s(f, g) ∨
      ∃ t ∈ s(f, g),
        (hypercubicLattice 2).Adj (phb_doubleDualShift q) t := by
  rcases hinc with hp | hq
  · exact Or.inr ⟨phb_doubleDualShift p, hp,
      (phb_doubleDualShift_latAdj.mpr hpq).symm⟩
  · exact Or.inl hq


theorem rlc_twoChannelFullPhysical_twoArcNoGood_tetheredShiftedWalk
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y : Site 2}
    {c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
    {hx : x ∈ c.support} {hy : y ∈ c.support}
    (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt
      gamma gamma' omega c hx hy) :
    ∃ (ur vr ul vl A B : Site 2)
      (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk x ur)
      (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph
        gamma gamma' omega).Walk y ul)
      (W : (hypercubicLattice 2).Walk A B),
      (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧
        (faceBoundaryGraph
          (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧
        s(ur, vr) ≠ s(ul, vl) ∧
        (RlcTwoChannelFullPhysicalRightArcBadLocation
            gamma gamma' (rlc_dualReflect A) ∨
          ∃ p : Site 2,
            RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
              A = phb_doubleDualShift p) ∧
        (RlcTwoChannelFullPhysicalLeftArcTargetBadLocation
            gamma gamma' (rlc_dualReflect B) ∨
          ∃ p : Site 2,
            RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
              B = phb_doubleDualShift p) ∧
        ∀ z ∈ W.support,
          z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
  obtain ⟨ur, vr, ul, vl, a, b, qr, ql, W, hurv, hulv, hne,
      hclassR, hclassL, _haEdge, _hbEdge, hWBox, _hWSource⟩ :=
    rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk hbad
  have htetherR :=
    rlc_twoChannelFullPhysical_rightArcShiftedBad_endpoint_tether
      hurv hclassR
  have htetherL :=
    rlc_twoChannelFullPhysical_leftArcShiftedBad_endpoint_tether
      hulv hclassL
  obtain ⟨A, hAClass, haA⟩ : ∃ A : Site 2,
      (RlcTwoChannelFullPhysicalRightArcBadLocation
          gamma gamma' (rlc_dualReflect A) ∨
        ∃ p : Site 2,
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
            A = phb_doubleDualShift p) ∧
      (a = A ∨ (hypercubicLattice 2).Adj a A) := by
    rcases htetherR with ⟨t, hloc, hat⟩ | ⟨p, hloc, hap⟩
    · exact ⟨t, Or.inl hloc, hat⟩
    · exact ⟨phb_doubleDualShift p, Or.inr ⟨p, hloc, rfl⟩, hap⟩
  obtain ⟨B, hBClass, hbB⟩ : ∃ B : Site 2,
      (RlcTwoChannelFullPhysicalLeftArcTargetBadLocation
          gamma gamma' (rlc_dualReflect B) ∨
        ∃ p : Site 2,
          RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧
            B = phb_doubleDualShift p) ∧
      (b = B ∨ (hypercubicLattice 2).Adj b B) := by
    rcases htetherL with ⟨t, hloc, hbt⟩ | ⟨p, hloc, hbp⟩
    · exact ⟨t, Or.inl hloc, hbt⟩
    · exact ⟨phb_doubleDualShift p, Or.inr ⟨p, hloc, rfl⟩, hbp⟩
  obtain ⟨W', hW'⟩ := rlc_walk_between_tethers W haA hbB
  have hinner {z : Site 2}
      (hz : z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) :
      z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rw [mem_rect] at hz ⊢
    omega
  have hABox : A ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases haA with rfl | haA
    · exact hinner (hWBox a W.start_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox a W.start_mem_support) haA
      rw [mem_rect] at h ⊢
      omega
  have hBBox : B ∈
      rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
    rcases hbB with rfl | hbB
    · exact hinner (hWBox b W.end_mem_support)
    · have h := rlc_neighbor_mem_expandedRect
        (hWBox b W.end_mem_support) hbB
      rw [mem_rect] at h ⊢
      omega
  refine ⟨ur, vr, ul, vl, A, B, qr, ql, W', hurv, hulv, hne,
    hAClass, hBClass, ?_⟩
  intro z hz
  rcases hW' z hz with rfl | rfl | hz
  · exact hABox
  · exact hBBox
  · exact hinner (hWBox z hz)


end
end StatMech.Universality
