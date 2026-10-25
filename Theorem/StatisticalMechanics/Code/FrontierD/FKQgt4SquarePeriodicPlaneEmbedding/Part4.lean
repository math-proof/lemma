/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part4
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.FK.PeriodicPlanar

noncomputable section

theorem squareOffsetEdgeArc_injective (offset : Complex)
    {x y : Site 2} (hxy : square.graph.Adj x y) :
    Function.Injective (squareOffsetEdgeArc offset hxy) := by
  apply Path.segment_injective_of_ne
  exact (squareOffsetVertex offset).injective.ne hxy.ne

theorem squareOffsetEdgeArc_symm (offset : Complex)
    {x y : Site 2} (hxy : square.graph.Adj x y) :
    Set.range (squareOffsetEdgeArc offset hxy.symm) =
      Set.range (squareOffsetEdgeArc offset hxy) := by
  rw [squareOffsetEdgeArc, squareOffsetEdgeArc, ← Path.segment_symm,
    Path.symm_range]

theorem squareOffsetEdgeArc_shift (offset : Complex) (z : Site 2)
    {x y : Site 2} (hxy : square.graph.Adj x y) :
    Set.range (squareOffsetEdgeArc offset ((square.shift_adj z x y).2 hxy)) =
      (fun p => p + squareComplexPeriod z) ''
        Set.range (squareOffsetEdgeArc offset hxy) := by
  change Set.range (Path.segment
      (squareOffsetVertex offset (siteTranslate z x))
      (squareOffsetVertex offset (siteTranslate z y))) = _
  rw [squareOffsetVertex_shift, squareOffsetVertex_shift]
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨squareOffsetEdgeArc offset hxy t, ⟨t, rfl⟩, ?_⟩
    simp only [squareOffsetEdgeArc, Path.segment_apply,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨t, ?_⟩
    simp only [squareOffsetEdgeArc, Path.segment_apply,
      AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module

theorem squareSite_eq_iff (x y : Site 2) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> assumption

theorem affineInt_mem_interval (a b : Int) (t : unitInterval) :
    ((min a b : Int) : Real) ≤ (t : Real) * (b - a) + a ∧
      (t : Real) * (b - a) + a ≤ ((max a b : Int) : Real) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab]
    have habR : (a : Real) ≤ b := by exact_mod_cast hab
    constructor <;> nlinarith [habR, t.2.1, t.2.2]
  · rw [min_eq_right hba, max_eq_left hba]
    have hbaR : (b : Real) ≤ a := by exact_mod_cast hba
    constructor <;> nlinarith [hbaR, t.2.1, t.2.2]

@[simp] theorem squareOffsetSegment_re (offset : Complex) (x y : Site 2)
    (t : unitInterval) :
    (Path.segment (squareOffsetVertex offset x)
      (squareOffsetVertex offset y) t).re =
        (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) + offset.re := by
  change (((t : Real) • ((squareComplexPoint y + offset) -
      (squareComplexPoint x + offset)) + (squareComplexPoint x + offset))).re = _
  simp only [Complex.real_smul, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    squareComplexPoint_re]
  ring

@[simp] theorem squareOffsetSegment_im (offset : Complex) (x y : Site 2)
    (t : unitInterval) :
    (Path.segment (squareOffsetVertex offset x)
      (squareOffsetVertex offset y) t).im =
        (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) + offset.im := by
  change (((t : Real) • ((squareComplexPoint y + offset) -
      (squareComplexPoint x + offset)) + (squareComplexPoint x + offset))).im = _
  simp only [Complex.real_smul, Complex.sub_im, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    squareComplexPoint_im]
  ring

theorem squareEdges_commonEndpoint_of_box_overlap
    {x y z w : Site 2}
    (hxy : square.graph.Adj x y) (hzw : square.graph.Adj z w)
    (h00 : min (x 0) (y 0) ≤ max (z 0) (w 0))
    (h01 : min (z 0) (w 0) ≤ max (x 0) (y 0))
    (h10 : min (x 1) (y 1) ≤ max (z 1) (w 1))
    (h11 : min (z 1) (w 1) ≤ max (x 1) (y 1)) :
    x = z ∨ x = w ∨ y = z ∨ y = w := by
  rw [show square.graph = hypercubicLattice 2 by rfl] at hxy hzw
  rw [squareSite_eq_iff, squareSite_eq_iff,
    squareSite_eq_iff, squareSite_eq_iff]
  rcases adj_cases hxy with hxy | hxy <;>
    rcases adj_cases hzw with hzw | hzw <;> omega

theorem squareNeighborSegments_inter_eq
    (offset : Complex) {v a b : Site 2}
    (hva : square.graph.Adj v a) (hvb : square.graph.Adj v b)
    (hab : a ≠ b) {p : Complex}
    (hpa : p ∈ Set.range (Path.segment
      (squareOffsetVertex offset v) (squareOffsetVertex offset a)))
    (hpb : p ∈ Set.range (Path.segment
      (squareOffsetVertex offset v) (squareOffsetVertex offset b))) :
    p = squareOffsetVertex offset v := by
  obtain ⟨t, rfl⟩ := hpa
  obtain ⟨u, hu⟩ := hpb
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp only [squareOffsetSegment_re] at hre
  simp only [squareOffsetSegment_im] at him
  rw [show square.graph = hypercubicLattice 2 by rfl] at hva hvb
  rcases adj_neighbor_cases a v hva.symm with ha | ha | ha | ha <;>
    rcases adj_neighbor_cases b v hvb.symm with hb | hb | hb | hb <;>
    subst a <;> subst b
  all_goals
    simp only [Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_add, Int.cast_neg, Int.cast_one, add_zero] at hre him
  all_goals try { exact (hab rfl).elim }
  all_goals
    ring_nf at hre him
    have htR : (t : Real) = 0 := by
      nlinarith [t.2.1, t.2.2, u.2.1, u.2.2]
    have ht : t = 0 := Subtype.ext htR
    rw [ht]
    exact (Path.segment (squareOffsetVertex offset v)
      (squareOffsetVertex offset _)).source

theorem mem_range_squareOffsetSegment_symm (offset : Complex) (x y : Site 2)
    {p : Complex}
    (hp : p ∈ Set.range (Path.segment
      (squareOffsetVertex offset x) (squareOffsetVertex offset y))) :
    p ∈ Set.range (Path.segment
      (squareOffsetVertex offset y) (squareOffsetVertex offset x)) := by
  have hEq : Set.range (Path.segment
      (squareOffsetVertex offset y) (squareOffsetVertex offset x)) =
      Set.range (Path.segment
        (squareOffsetVertex offset x) (squareOffsetVertex offset y)) := by
    rw [← Path.segment_symm, Path.symm_range]
  rw [hEq]
  exact hp

theorem squareOffsetEdgeArc_intersection (offset : Complex)
    {x y z w : Site 2}
    (hxy : square.graph.Adj x y) (hzw : square.graph.Adj z w) (p : Complex)
    (hne : s(x, y) ≠ s(z, w))
    (hp : p ∈ Set.range (squareOffsetEdgeArc offset hxy))
    (hq : p ∈ Set.range (squareOffsetEdgeArc offset hzw)) :
    ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧
      squareOffsetVertex offset v = p := by
  have hpMem := hp
  have hqMem := hq
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, hu⟩ := hq
  have hre := congrArg Complex.re (hu.trans ht.symm)
  have him := congrArg Complex.im (hu.trans ht.symm)
  simp only [squareOffsetEdgeArc, squareOffsetSegment_re] at hre
  simp only [squareOffsetEdgeArc, squareOffsetSegment_im] at him
  have hxy0 := affineInt_mem_interval (x 0) (y 0) t
  have hzw0 := affineInt_mem_interval (z 0) (w 0) u
  have hxy1 := affineInt_mem_interval (x 1) (y 1) t
  have hzw1 := affineInt_mem_interval (z 1) (w 1) u
  have h00R : ((min (x 0) (y 0) : Int) : Real) ≤
      ((max (z 0) (w 0) : Int) : Real) := by
    calc
      ((min (x 0) (y 0) : Int) : Real) ≤
          (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) := hxy0.1
      _ = (u : Real) * ((w 0 : Real) - (z 0 : Real)) + (z 0 : Real) := by
        linarith
      _ ≤ ((max (z 0) (w 0) : Int) : Real) := hzw0.2
  have h01R : ((min (z 0) (w 0) : Int) : Real) ≤
      ((max (x 0) (y 0) : Int) : Real) := by
    calc
      ((min (z 0) (w 0) : Int) : Real) ≤
          (u : Real) * ((w 0 : Real) - (z 0 : Real)) + (z 0 : Real) := hzw0.1
      _ = (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) := by
        linarith
      _ ≤ ((max (x 0) (y 0) : Int) : Real) := hxy0.2
  have h10R : ((min (x 1) (y 1) : Int) : Real) ≤
      ((max (z 1) (w 1) : Int) : Real) := by
    calc
      ((min (x 1) (y 1) : Int) : Real) ≤
          (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) := hxy1.1
      _ = (u : Real) * ((w 1 : Real) - (z 1 : Real)) + (z 1 : Real) := by
        linarith
      _ ≤ ((max (z 1) (w 1) : Int) : Real) := hzw1.2
  have h11R : ((min (z 1) (w 1) : Int) : Real) ≤
      ((max (x 1) (y 1) : Int) : Real) := by
    calc
      ((min (z 1) (w 1) : Int) : Real) ≤
          (u : Real) * ((w 1 : Real) - (z 1 : Real)) + (z 1 : Real) := hzw1.1
      _ = (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) := by
        linarith
      _ ≤ ((max (x 1) (y 1) : Int) : Real) := hxy1.2
  have hcommon := squareEdges_commonEndpoint_of_box_overlap hxy hzw
    (by exact_mod_cast h00R) (by exact_mod_cast h01R)
    (by exact_mod_cast h10R) (by exact_mod_cast h11R)
  rcases hcommon with hxz | hxw | hyz | hyw
  · subst z
    have hyw : y ≠ w := by
      intro hyw
      subst w
      exact hne rfl
    have hv := squareNeighborSegments_inter_eq offset hxy hzw hyw hpMem hqMem
    exact ⟨x, Or.inl rfl, Or.inl rfl, hv.symm⟩
  · subst w
    have hyz : y ≠ z := by
      intro hyz
      subst z
      exact hne Sym2.eq_swap
    have hq' := mem_range_squareOffsetSegment_symm offset z x hqMem
    have hv := squareNeighborSegments_inter_eq offset hxy hzw.symm hyz hpMem hq'
    exact ⟨x, Or.inl rfl, Or.inr rfl, hv.symm⟩
  · subst z
    have hxw : x ≠ w := by
      intro hxw
      subst w
      exact hne Sym2.eq_swap
    have hp' := mem_range_squareOffsetSegment_symm offset x y hpMem
    have hv := squareNeighborSegments_inter_eq offset hxy.symm hzw hxw hp' hqMem
    exact ⟨y, Or.inr rfl, Or.inl rfl, hv.symm⟩
  · subst w
    have hxz : x ≠ z := by
      intro hxz
      subst z
      exact hne rfl
    have hp' := mem_range_squareOffsetSegment_symm offset x y hpMem
    have hq' := mem_range_squareOffsetSegment_symm offset z y hqMem
    have hv := squareNeighborSegments_inter_eq offset hxy.symm hzw.symm hxz hp' hq'
    exact ⟨y, Or.inr rfl, Or.inr rfl, hv.symm⟩

theorem squareOffsetEdgeArc_disjoint (offset : Complex)
    {x y z w : Site 2}
    (hxy : square.graph.Adj x y) (hzw : square.graph.Adj z w)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) :
    Disjoint (Set.range (squareOffsetEdgeArc offset hxy))
      (Set.range (squareOffsetEdgeArc offset hzw)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hne : s(x, y) ≠ s(z, w) := by
    intro he
    rw [Sym2.eq_iff] at he
    rcases he with he | he
    · exact hxz he.1
    · exact hxw he.1
  obtain ⟨v, hvxy, hvzw, _⟩ :=
    squareOffsetEdgeArc_intersection offset hxy hzw p hne hp hq
  rcases hvxy with rfl | rfl <;> rcases hvzw with rfl | rfl
  · exact hxz rfl
  · exact hxw rfl
  · exact hyz rfl
  · exact hyw rfl

theorem squareOffsetVertex_sub_norm_of_adj (offset : Complex)
    {x y : Site 2} (hxy : square.graph.Adj x y) :
    ‖(squareOffsetVertex offset x : Complex) - squareOffsetVertex offset y‖ = 1 := by
  have hy0 : Matrix.vecHead y = y 0 := rfl
  have hy1 : Matrix.vecHead (Matrix.vecTail y) = y 1 := rfl
  rw [show square.graph = hypercubicLattice 2 by rfl] at hxy
  rcases adj_neighbor_cases x y hxy with h | h | h | h <;> subst x
  · have heq : (squareOffsetVertex offset (y + ![1, 0]) : Complex) -
        squareOffsetVertex offset y = 1 := by
      apply Complex.ext <;>
        simp [squareOffsetVertex, squareComplexPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one, hy0, hy1]
    rw [heq, norm_one]
  · have heq : (squareOffsetVertex offset (y + ![-1, 0]) : Complex) -
        squareOffsetVertex offset y = -1 := by
      apply Complex.ext <;>
        simp [squareOffsetVertex, squareComplexPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one, hy0, hy1]
    rw [heq, norm_neg, norm_one]
  · have heq : (squareOffsetVertex offset (y + ![0, 1]) : Complex) -
        squareOffsetVertex offset y = Complex.I := by
      apply Complex.ext <;>
        simp [squareOffsetVertex, squareComplexPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one, hy0, hy1]
    rw [heq, Complex.norm_I]
  · have heq : (squareOffsetVertex offset (y + ![0, -1]) : Complex) -
        squareOffsetVertex offset y = -Complex.I := by
      apply Complex.ext <;>
        simp [squareOffsetVertex, squareComplexPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one, hy0, hy1]
    rw [heq, norm_neg, Complex.norm_I]

theorem squareOffsetVertex_sub_segment_norm_le_one (offset : Complex)
    {x y : Site 2} (hxy : square.graph.Adj x y) (t : unitInterval) :
    ‖(squareOffsetVertex offset x : Complex) -
        Path.segment (squareOffsetVertex offset x)
          (squareOffsetVertex offset y) t‖ ≤ 1 := by
  change ‖(squareOffsetVertex offset x : Complex) -
    ((t : Real) • ((squareOffsetVertex offset y : Complex) -
      squareOffsetVertex offset x) + squareOffsetVertex offset x)‖ ≤ 1
  calc
    _ = ‖(t : Real) • ((squareOffsetVertex offset x : Complex) -
        squareOffsetVertex offset y)‖ := by
      congr 1
      module
    _ = |(t : Real)| * ‖(squareOffsetVertex offset x : Complex) -
        squareOffsetVertex offset y‖ := norm_smul _ _
    _ = (t : Real) := by
      rw [abs_of_nonneg t.2.1, squareOffsetVertex_sub_norm_of_adj offset hxy, mul_one]
    _ ≤ 1 := t.2.2

theorem squareOffsetEndpoint_norm_le_of_mem_segment (offset : Complex)
    {x y : Site 2} (hxy : square.graph.Adj x y) {p : Complex}
    (hp : p ∈ Set.range (Path.segment
      (squareOffsetVertex offset x) (squareOffsetVertex offset y))) :
    ‖(squareOffsetVertex offset x : Complex)‖ ≤ ‖p‖ + 1 := by
  obtain ⟨t, rfl⟩ := hp
  calc
    ‖(squareOffsetVertex offset x : Complex)‖ =
        ‖((squareOffsetVertex offset x : Complex) -
          Path.segment (squareOffsetVertex offset x)
            (squareOffsetVertex offset y) t) +
          Path.segment (squareOffsetVertex offset x)
            (squareOffsetVertex offset y) t‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(squareOffsetVertex offset x : Complex) -
          Path.segment (squareOffsetVertex offset x)
            (squareOffsetVertex offset y) t‖ +
        ‖Path.segment (squareOffsetVertex offset x)
          (squareOffsetVertex offset y) t‖ := norm_add_le _ _
    _ ≤ 1 + ‖Path.segment (squareOffsetVertex offset x)
          (squareOffsetVertex offset y) t‖ :=
      by
        gcongr
        exact squareOffsetVertex_sub_segment_norm_le_one offset hxy t
    _ = ‖Path.segment (squareOffsetVertex offset x)
          (squareOffsetVertex offset y) t‖ + 1 := add_comm _ _

theorem squareOffsetEdgeArc_locallyFinite (offset : Complex)
    (K : Set Complex) (hK : IsCompact K) :
    {xy : Site 2 × Site 2 | ∃ hxy : square.graph.Adj xy.1 xy.2,
      (Set.range (squareOffsetEdgeArc offset hxy) ∩ K).Nonempty}.Finite := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  let S : Set (Site 2) :=
    {x | ‖(squareOffsetVertex offset x : Complex)‖ ≤ C + 1}
  have hS : S.Finite := squareOffsetVertex_proper offset (C + 1)
  apply (hS.prod hS).subset
  rintro ⟨x, y⟩ ⟨hxy, p, hpArc, hpK⟩
  change x ∈ S ∧ y ∈ S
  constructor
  · change ‖(squareOffsetVertex offset x : Complex)‖ ≤ C + 1
    calc
      ‖(squareOffsetVertex offset x : Complex)‖ ≤ ‖p‖ + 1 :=
        squareOffsetEndpoint_norm_le_of_mem_segment offset hxy hpArc
      _ ≤ C + 1 := by gcongr; exact hC p hpK
  · change ‖(squareOffsetVertex offset y : Complex)‖ ≤ C + 1
    have hpRev := mem_range_squareOffsetSegment_symm offset x y hpArc
    calc
      ‖(squareOffsetVertex offset y : Complex)‖ ≤ ‖p‖ + 1 :=
        squareOffsetEndpoint_norm_le_of_mem_segment offset hxy.symm hpRev
      _ ≤ C + 1 := by gcongr; exact hC p hpK


end
end StatMech.FrontierD
