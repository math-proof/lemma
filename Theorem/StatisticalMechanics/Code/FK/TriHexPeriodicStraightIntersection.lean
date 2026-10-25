/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexPeriodicStraightIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.TriHexPeriodicPlaneEmbedding.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

@[simp] theorem triangularCanonicalSegment_re
    (x : Site 2) (i : Fin 3) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i)) t).re =
        (x 0 : Real) + (t : Real) * (triangularStep i 0 : Real) := by
  change (((t : Real) •
    (triHexPlanePeriod (x + triangularStep i) - triHexPlanePeriod x) +
      triHexPlanePeriod x)).re = _
  rw [map_add]
  simp [Complex.real_smul]
  ring

@[simp] theorem triangularCanonicalSegment_im
    (x : Site 2) (i : Fin 3) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i)) t).im =
        (x 1 : Real) + (t : Real) * (triangularStep i 1 : Real) := by
  change (((t : Real) •
    (triHexPlanePeriod (x + triangularStep i) - triHexPlanePeriod x) +
      triHexPlanePeriod x)).im = _
  rw [map_add]
  simp [Complex.real_smul]
  ring

theorem affineInt_mem_interval (a b : Int) (t : unitInterval) :
    ((min a b : Int) : Real) <=
        (t : Real) * ((b : Real) - (a : Real)) + (a : Real) /\
      (t : Real) * ((b : Real) - (a : Real)) + (a : Real) <=
        ((max a b : Int) : Real) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    have habR : (a : Real) <= b := by exact_mod_cast hab
    constructor <;> nlinarith [t.2.1, t.2.2]
  · rw [min_eq_right hba, max_eq_left hba]
    have hbaR : (b : Real) <= a := by exact_mod_cast hba
    constructor <;> nlinarith [t.2.1, t.2.2]


theorem triangularCanonicalSegments_commonEndpoint
    (x z : Site 2) (i j : Fin 3) (p : Complex)
    (hp : p ∈ Set.range (Path.segment (triangularPlaneVertex x)
      (triangularPlaneVertex (x + triangularStep i))))
    (hq : p ∈ Set.range (Path.segment (triangularPlaneVertex z)
      (triangularPlaneVertex (z + triangularStep j)))) :
    x = z ∨ x = z + triangularStep j ∨
      x + triangularStep i = z ∨
      x + triangularStep i = z + triangularStep j := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, hu⟩ := hq
  have hre := congrArg Complex.re (ht.trans hu.symm)
  have him := congrArg Complex.im (ht.trans hu.symm)
  simp only [triangularCanonicalSegment_re] at hre
  simp only [triangularCanonicalSegment_im] at him
  let y := x + triangularStep i
  let w := z + triangularStep j
  have h0eq :
      (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) =
        (u : Real) * ((w 0 : Real) - (z 0 : Real)) + (z 0 : Real) := by
    dsimp [y, w]
    simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left,
      add_comm] using hre
  have h1eq :
      (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) =
        (u : Real) * ((w 1 : Real) - (z 1 : Real)) + (z 1 : Real) := by
    dsimp [y, w]
    simpa only [Pi.add_apply, Int.cast_add, add_sub_cancel_left,
      add_comm] using him
  have hx0 := affineInt_mem_interval (x 0) (y 0) t
  have hz0 := affineInt_mem_interval (z 0) (w 0) u
  have hx1 := affineInt_mem_interval (x 1) (y 1) t
  have hz1 := affineInt_mem_interval (z 1) (w 1) u
  have hxs := affineInt_mem_interval (x 0 + x 1) (y 0 + y 1) t
  have hzs := affineInt_mem_interval (z 0 + z 1) (w 0 + w 1) u
  have hseq :
      (t : Real) * (((y 0 + y 1 : Int) : Real) -
          ((x 0 + x 1 : Int) : Real)) + ((x 0 + x 1 : Int) : Real) =
        (u : Real) * (((w 0 + w 1 : Int) : Real) -
          ((z 0 + z 1 : Int) : Real)) + ((z 0 + z 1 : Int) : Real) := by
    push_cast
    linarith
  have h00R : ((min (x 0) (y 0) : Int) : Real) <=
      ((max (z 0) (w 0) : Int) : Real) := hx0.1.trans (h0eq.trans_le hz0.2)
  have h01R : ((min (z 0) (w 0) : Int) : Real) <=
      ((max (x 0) (y 0) : Int) : Real) := hz0.1.trans (h0eq.symm.trans_le hx0.2)
  have h10R : ((min (x 1) (y 1) : Int) : Real) <=
      ((max (z 1) (w 1) : Int) : Real) := hx1.1.trans (h1eq.trans_le hz1.2)
  have h11R : ((min (z 1) (w 1) : Int) : Real) <=
      ((max (x 1) (y 1) : Int) : Real) := hz1.1.trans (h1eq.symm.trans_le hx1.2)
  have hs0R : ((min (x 0 + x 1) (y 0 + y 1) : Int) : Real) <=
      ((max (z 0 + z 1) (w 0 + w 1) : Int) : Real) :=
    hxs.1.trans (hseq.trans_le hzs.2)
  have hs1R : ((min (z 0 + z 1) (w 0 + w 1) : Int) : Real) <=
      ((max (x 0 + x 1) (y 0 + y 1) : Int) : Real) :=
    hzs.1.trans (hseq.symm.trans_le hxs.2)
  have h00 : min (x 0) (y 0) <= max (z 0) (w 0) := by exact_mod_cast h00R
  have h01 : min (z 0) (w 0) <= max (x 0) (y 0) := by exact_mod_cast h01R
  have h10 : min (x 1) (y 1) <= max (z 1) (w 1) := by exact_mod_cast h10R
  have h11 : min (z 1) (w 1) <= max (x 1) (y 1) := by exact_mod_cast h11R
  have hs0 : min (x 0 + x 1) (y 0 + y 1) <=
      max (z 0 + z 1) (w 0 + w 1) := by exact_mod_cast hs0R
  have hs1 : min (z 0 + z 1) (w 0 + w 1) <=
      max (x 0 + x 1) (y 0 + y 1) := by exact_mod_cast hs1R
  dsimp [y, w] at h00 h01 h10 h11 hs0 hs1
  have hxHead : Matrix.vecHead x = x 0 := rfl
  have hxTail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
  have hzHead : Matrix.vecHead z = z 0 := rfl
  have hzTail : Matrix.vecHead (Matrix.vecTail z) = z 1 := rfl
  fin_cases i <;> fin_cases j
  all_goals
    simp [triangularStep, funext_iff, hxHead, hxTail, hzHead, hzTail]
      at h00 h01 h10 h11 hs0 hs1 ⊢
  all_goals omega

@[simp] theorem triangularSegment_re
    (x y : Site 2) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).re =
      (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) := by
  change (((t : Real) • (triHexPlanePeriod y - triHexPlanePeriod x) +
    triHexPlanePeriod x)).re = _
  simp [Complex.real_smul]

@[simp] theorem triangularSegment_im
    (x y : Site 2) (t : unitInterval) :
    (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y) t).im =
      (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) := by
  change (((t : Real) • (triHexPlanePeriod y - triHexPlanePeriod x) +
    triHexPlanePeriod x)).im = _
  simp [Complex.real_smul]

theorem mem_range_triangularSegment_symm (x y : Site 2) {p : Complex}
    (hp : p ∈ Set.range
      (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y))) :
    p ∈ Set.range
      (Path.segment (triangularPlaneVertex y) (triangularPlaneVertex x)) := by
  rw [Path.range_segment, segment_symm]
  simpa only [Path.range_segment] using hp


theorem triangularNeighborSegments_inter_eq
    {v a b : Site 2}
    (hva : triangularGraph.Adj v a) (hvb : triangularGraph.Adj v b)
    (hab : Ne a b) {p : Complex}
    (hpa : p ∈ Set.range
      (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex a)))
    (hpb : p ∈ Set.range
      (Path.segment (triangularPlaneVertex v) (triangularPlaneVertex b))) :
    p = triangularPlaneVertex v := by
  obtain ⟨t, rfl⟩ := hpa
  obtain ⟨u, hu⟩ := hpb
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [triangularSegment_re] at hre
  simp only [triangularSegment_im] at him
  obtain ⟨ia, _hia, rfl⟩ := Finset.mem_image.mp
    (triangular_mem_candidates_of_adj hva)
  obtain ⟨ib, _hib, rfl⟩ := Finset.mem_image.mp
    (triangular_mem_candidates_of_adj hvb)
  rcases ia with ⟨i, bi⟩
  rcases ib with ⟨j, bj⟩
  fin_cases i <;> fin_cases j <;> cases bi <;> cases bj
  all_goals
    simp [triangularNeighbor, triangularStep, funext_iff] at hre him hab
  all_goals
    have htR : (t : Real) = 0 := by
      first
      | exact hre
      | exact congrArg Subtype.val hre
      | exact him
      | exact congrArg Subtype.val him
      | have huR : (u : Real) = 0 := congrArg Subtype.val him
        linarith [hre, huR]
      | have huR : (u : Real) = 0 := congrArg Subtype.val hre
        linarith [him, huR]
      | linarith [hre, him, t.2.1, u.2.1]
    have ht : t = 0 := Subtype.ext htR
    rw [ht]
    exact (Path.segment (triangularPlaneVertex v)
      (triangularPlaneVertex _)).source

theorem triangularEdges_commonEndpoint_of_intersection
    {x y z w : Site 2}
    (hxy : triangularGraph.Adj x y) (hzw : triangularGraph.Adj z w)
    (p : Complex)
    (hp : p ∈ Set.range (triangularStraightEdgeArc hxy))
    (hq : p ∈ Set.range (triangularStraightEdgeArc hzw)) :
    ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) := by
  let exy : triangularGraph.edgeSet := ⟨s(x, y), hxy⟩
  let ezw : triangularGraph.edgeSet := ⟨s(z, w), hzw⟩
  let a := triangularEdgeChartEquiv.symm exy
  let b := triangularEdgeChartEquiv.symm ezw
  have ha : triangularIndexedEdge a = s(x, y) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply exy)
    exact h
  have hb : triangularIndexedEdge b = s(z, w) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply ezw)
    exact h
  rw [triangularIndexedEdge, Sym2.eq_iff] at ha hb
  have hp0 : p ∈ Set.range
      (Path.segment (triangularPlaneVertex x) (triangularPlaneVertex y)) := hp
  have hq0 : p ∈ Set.range
      (Path.segment (triangularPlaneVertex z) (triangularPlaneVertex w)) := hq
  rcases ha with ha | ha
  · have hp' : p ∈ Set.range (Path.segment
    (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
      rw [ha.2, ha.1]
      exact hp0
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inl ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inl ha.1, Or.inr (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_triangularSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inl ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inl ha.1, Or.inl (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inr ha.2,
          Or.inl (h.trans hb.2)⟩
  · have hpRev := mem_range_triangularSegment_symm x y hp0
    have hp' : p ∈ Set.range (Path.segment
        (triangularPlaneVertex a.1)
        (triangularPlaneVertex (a.1 + triangularStep a.2))) := by
      rw [ha.2, ha.1]
      exact hpRev
    rcases hb with hb | hb
    · have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hq0
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inr ha.1, Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inr ha.1, Or.inr (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inl (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inr (h.trans hb.2)⟩
    · have hqRev := mem_range_triangularSegment_symm z w hq0
      have hq' : p ∈ Set.range (Path.segment
          (triangularPlaneVertex b.1)
          (triangularPlaneVertex (b.1 + triangularStep b.2))) := by
        rw [hb.2, hb.1]
        exact hqRev
      rcases triangularCanonicalSegments_commonEndpoint a.1 b.1 a.2 b.2 p hp' hq'
        with h | h | h | h
      · exact ⟨a.1, Or.inr ha.1, Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1, Or.inr ha.1, Or.inl (h.trans hb.2)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inr (h.trans hb.1)⟩
      · exact ⟨a.1 + triangularStep a.2, Or.inl ha.2,
          Or.inl (h.trans hb.2)⟩


theorem triangularStraightEdgeIntersection :
    TriangularStraightEdgeIntersectionProperty := by
  intro x y z w hxy hzw p hne hp hq
  have hpMem := hp
  have hqMem := hq
  obtain ⟨v, hvxy, hvzw⟩ :=
    triangularEdges_commonEndpoint_of_intersection hxy hzw p hp hq
  rcases hvxy with hvx | hvy
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hyw : Ne y w := by
        intro hyw
        subst w
        exact hne rfl
      have hv := triangularNeighborSegments_inter_eq hxy hzw hyw hpMem hqMem
      exact ⟨x, Or.inl rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hyz : Ne y z := by
        intro hyz
        subst z
        exact hne Sym2.eq_swap
      have hq' := mem_range_triangularSegment_symm z x hqMem
      have hv := triangularNeighborSegments_inter_eq hxy hzw.symm hyz hpMem hq'
      exact ⟨x, Or.inl rfl, Or.inr rfl, hv.symm⟩
  · subst v
    rcases hvzw with hvz | hvw
    · subst z
      have hxw : Ne x w := by
        intro hxw
        subst w
        exact hne Sym2.eq_swap
      have hp' := mem_range_triangularSegment_symm x y hpMem
      have hv := triangularNeighborSegments_inter_eq hxy.symm hzw hxw hp' hqMem
      exact ⟨y, Or.inr rfl, Or.inl rfl, hv.symm⟩
    · subst w
      have hxz : Ne x z := by
        intro hxz
        subst z
        exact hne rfl
      have hp' := mem_range_triangularSegment_symm x y hpMem
      have hq' := mem_range_triangularSegment_symm z y hqMem
      have hv := triangularNeighborSegments_inter_eq hxy.symm hzw.symm hxz hp' hq'
      exact ⟨y, Or.inr rfl, Or.inr rfl, hv.symm⟩


end StatMech.FK.PeriodicPlanar
