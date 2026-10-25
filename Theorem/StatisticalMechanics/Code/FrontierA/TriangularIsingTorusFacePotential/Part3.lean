/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part3
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularPositiveEdgeReconstruction_eq
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
    triangularPositiveEdgeReconstruction L F = F := by
  apply Finset.ext
  intro edge
  constructor
  · intro hedge
    rw [triangularPositiveEdgeReconstruction, Finset.mem_biUnion] at hedge
    obtain ⟨a, -, hedge⟩ := hedge
    rw [Finset.mem_image] at hedge
    obtain ⟨p, hp, rfl⟩ := hedge
    exact (Finset.mem_filter.mp hp).2
  · intro hedge
    have hedgeGraph := hF hedge
    rw [SimpleGraph.mem_edgeFinset] at hedgeGraph
    induction edge using Sym2.ind with
    | _ u v =>
      let dart : (triangularTorusGraph L).Dart := ⟨(u, v), hedgeGraph⟩
      let d : triangularTorusDart L := (triangularTorusDartEquiv L).symm dart
      have hdart : triangularTorusDartEquiv L d = dart := by simp [d]
      have hdedge : (triangularTorusDartEquiv L d).edge = s(u, v) := by
        rw [hdart]
        rfl
      rcases d with ⟨p, a⟩
      fin_cases a
      · let r := triangularTorusDartReverse L (p, 0)
        have hrdir : r.2 = 1 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge
      · let r := triangularTorusDartReverse L (p, 2)
        have hrdir : r.2 = 3 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge
      · let r := triangularTorusDartReverse L (p, 4)
        have hrdir : r.2 = 5 := by
          simp [r, triangularTorusDartReverse,
            triangularTorusDirectionReverse]
        have hredge : (triangularTorusDartEquiv L r).edge = s(u, v) := by
          rw [triangularTorusDartEquiv_reverse, SimpleGraph.Dart.edge_symm]
          exact hdedge
        refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using
            (hredge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection, hrdir] using hredge
      · refine Finset.mem_biUnion.mpr ⟨2, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_image]
        refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using
            (hdedge.symm ▸ hedge)
        · simpa [triangularPositiveEdge,
            triangularTorusPositiveDirection] using hdedge

theorem triangularPositiveEdgeReconstruction_pairwiseDisjoint
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun a => (triangularPositiveEdgeSources L F a).image
        (triangularPositiveEdge L a)) := by
  intro a _ b _ hab
  change Disjoint
    ((triangularPositiveEdgeSources L F a).image
      (triangularPositiveEdge L a))
    ((triangularPositiveEdgeSources L F b).image
      (triangularPositiveEdge L b))
  rw [Finset.disjoint_left]
  intro edge hea heb
  rw [Finset.mem_image] at hea heb
  obtain ⟨p, -, rfl⟩ := hea
  obtain ⟨q, -, heq⟩ := heb
  have hnative := (triangularTorusPositiveEdge_eq_iff L p q a b).mp heq.symm
  exact hab hnative.2

theorem sum_triangularPositiveEdgeSources
    {A : Type*} [AddCommMonoid A]
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset)
    (f : Sym2 (ZMod L × ZMod L) → A) :
    (∑ edge ∈ F, f edge) =
      ∑ a : Fin 3, ∑ p ∈ triangularPositiveEdgeSources L F a,
        f (triangularPositiveEdge L a p) := by
  conv_lhs =>
    rw [← triangularPositiveEdgeReconstruction_eq L F hF]
  unfold triangularPositiveEdgeReconstruction
  rw [Finset.sum_biUnion
    (triangularPositiveEdgeReconstruction_pairwiseDisjoint L F)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image]
  intro p _ q _ hpq
  exact (triangularTorusPositiveEdge_eq_iff L p q a a).mp hpq |>.1

theorem triangularTorusXSeamEdge_positiveEdge_iff
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) :
    triangularTorusXSeamEdge L (triangularPositiveEdge L a p) ↔
      (a = 0 ∨ a = 2) ∧ p.1 = -1 := by
  unfold triangularPositiveEdge
  rw [triangularTorusXSeamEdge_dart_iff]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusXMovementDart, triangularTorusXMovementDirection,
      ons_xWrap]

theorem triangularTorusYSeamEdge_positiveEdge_iff
    (L : Nat) [Fact (2 < L)] (a : Fin 3)
    (p : ZMod L × ZMod L) :
    triangularTorusYSeamEdge L (triangularPositiveEdge L a p) ↔
      (a = 1 ∨ a = 2) ∧ p.2 = -1 := by
  unfold triangularPositiveEdge
  rw [triangularTorusYSeamEdge_dart_iff]
  fin_cases a <;>
    simp [triangularTorusPositiveDirection,
      triangularTorusYMovementDart, triangularTorusYMovementDirection,
      ons_yWrap]

theorem sum_positiveSources_first_seam
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    (∑ p ∈ triangularPositiveEdgeSources L F a,
        if p.1 = -1 then (1 : ZMod 2) else 0) =
      ∑ y : ZMod L,
        (ons_edgeBit F (triangularPositiveEdge L a (-1, y)) : ZMod 2) := by
  classical
  unfold triangularPositiveEdgeSources
  calc
    (∑ p ∈ Finset.univ.filter
        (fun p => triangularPositiveEdge L a p ∈ F),
        if p.1 = -1 then (1 : ZMod 2) else 0) =
      ∑ p : ZMod L × ZMod L,
        if triangularPositiveEdge L a p ∈ F then
          (if p.1 = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ x : ZMod L, ∑ y : ZMod L,
        if triangularPositiveEdge L a (x, y) ∈ F then
          (if x = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ y : ZMod L,
        if triangularPositiveEdge L a (-1, y) ∈ F then 1 else 0 := by
      rw [Finset.sum_eq_single (-1)]
      · apply Finset.sum_congr rfl
        intro y _
        simp
      · intro x _ hx
        apply Finset.sum_eq_zero
        intro y _
        simp [hx]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [ons_edgeBit]
      split <;> rfl

theorem sum_positiveSources_second_seam
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (a : Fin 3) :
    (∑ p ∈ triangularPositiveEdgeSources L F a,
        if p.2 = -1 then (1 : ZMod 2) else 0) =
      ∑ x : ZMod L,
        (ons_edgeBit F (triangularPositiveEdge L a (x, -1)) : ZMod 2) := by
  classical
  unfold triangularPositiveEdgeSources
  calc
    (∑ p ∈ Finset.univ.filter
        (fun p => triangularPositiveEdge L a p ∈ F),
        if p.2 = -1 then (1 : ZMod 2) else 0) =
      ∑ p : ZMod L × ZMod L,
        if triangularPositiveEdge L a p ∈ F then
          (if p.2 = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ x : ZMod L, ∑ y : ZMod L,
        if triangularPositiveEdge L a (x, y) ∈ F then
          (if y = -1 then (1 : ZMod 2) else 0) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : ZMod L,
        if triangularPositiveEdge L a (x, -1) ∈ F then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single (-1)]
      · simp
      · intro y _ hy
        simp [hy]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [ons_edgeBit]
      split <;> rfl

theorem triangularTorusEvenHomology_fst_cast_eq_sum
    (L : Nat) (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((triangularTorusEvenHomology L F).1 : ZMod 2) =
      ∑ edge ∈ F,
        if triangularTorusXSeamEdge L edge then (1 : ZMod 2) else 0 := by
  classical
  rw [Finset.sum_boole]
  apply ZMod.val_injective 2
  simp only [triangularTorusEvenHomology, ZMod.val_natCast]
  rfl

theorem triangularTorusEvenHomology_snd_cast_eq_sum
    (L : Nat) (F : Finset (Sym2 (ZMod L × ZMod L))) :
    ((triangularTorusEvenHomology L F).2 : ZMod 2) =
      ∑ edge ∈ F,
        if triangularTorusYSeamEdge L edge then (1 : ZMod 2) else 0 := by
  classical
  rw [Finset.sum_boole]
  apply ZMod.val_injective 2
  simp only [triangularTorusEvenHomology, ZMod.val_natCast]
  rfl

@[simp] theorem triangularPositiveEdge_zero
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 0 p = triangularTorusEastEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusEastEdge]

@[simp] theorem triangularPositiveEdge_one
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 1 p = triangularTorusNorthEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusNorthEdge]

@[simp] theorem triangularPositiveEdge_two
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularPositiveEdge L 2 p = triangularTorusNortheastEdge L p := by
  simp [triangularPositiveEdge, triangularTorusPositiveDirection,
    triangularTorusNortheastEdge]


theorem triangularSquareExpansion_evenHomology
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
    ons_evenHomology L (triangularSquareExpansion L F) =
      triangularTorusEvenHomology L F := by
  apply Prod.ext
  · apply Fin.ext
    have hcast :
        ((ons_evenHomology L (triangularSquareExpansion L F)).1 : ZMod 2) =
          ((triangularTorusEvenHomology L F).1 : ZMod 2) := by
      rw [ons_evenHomology_fst_cast_eq_xFlux,
        triangularTorusEvenHomology_fst_cast_eq_sum,
        sum_triangularPositiveEdgeSources L F hF]
      unfold ons_xFlux
      simp_rw [triangularSquareExpansion_horizontalBit]
      change (∑ y ∈ Finset.univ,
        ((ons_edgeBit F (triangularTorusEastEdge L (-1, y)) : ZMod 2) +
          ons_edgeBit F (triangularTorusNortheastEdge L (-1, y)))) = _
      rw [Finset.sum_add_distrib, Fin.sum_univ_three]
      simp_rw [triangularTorusXSeamEdge_positiveEdge_iff]
      simp only [Fin.isValue, Fin.reduceEq, one_ne_zero, or_false,
        false_or, or_self, true_or, or_true, true_and, false_and,
        ite_true, ite_false, zero_add, add_zero]
      rw [sum_positiveSources_first_seam L F 0,
        sum_positiveSources_first_seam L F 2]
      simp only [triangularPositiveEdge_zero,
        triangularPositiveEdge_two, Finset.sum_const_zero, add_zero]
      rfl
    exact congrArg (fun z : ZMod 2 => z.val) hcast
  · apply Fin.ext
    have hcast :
        ((ons_evenHomology L (triangularSquareExpansion L F)).2 : ZMod 2) =
          ((triangularTorusEvenHomology L F).2 : ZMod 2) := by
      rw [ons_evenHomology_snd_cast_eq_yFlux,
        triangularTorusEvenHomology_snd_cast_eq_sum,
        sum_triangularPositiveEdgeSources L F hF]
      unfold ons_yFlux
      simp_rw [triangularSquareExpansion_verticalBit]
      change (∑ x ∈ Finset.univ,
        ((ons_edgeBit F (triangularTorusNorthEdge L (x, -1)) : ZMod 2) +
          ons_edgeBit F
            (triangularTorusNortheastEdge L (x - 1, -1)))) = _
      rw [Finset.sum_add_distrib, Fin.sum_univ_three]
      simp_rw [triangularTorusYSeamEdge_positiveEdge_iff]
      simp only [Fin.isValue, Fin.reduceEq, one_ne_zero, or_false,
        false_or, or_self, true_or, or_true, true_and, false_and,
        ite_true, ite_false, zero_add, add_zero]
      rw [sum_positiveSources_second_seam L F 1,
        sum_positiveSources_second_seam L F 2]
      simp only [triangularPositiveEdge_one, triangularPositiveEdge_two,
        Finset.sum_const_zero, zero_add, add_zero]
      congr 1
      simpa [sub_eq_add_neg] using
        (Equiv.sum_comp (Equiv.addRight (-1 : ZMod L))
          (fun x : ZMod L =>
            (ons_edgeBit F
              (triangularTorusNortheastEdge L (x, -1)) : ZMod 2)))
    exact congrArg (fun z : ZMod 2 => z.val) hcast


end StatMech.FrontierA
