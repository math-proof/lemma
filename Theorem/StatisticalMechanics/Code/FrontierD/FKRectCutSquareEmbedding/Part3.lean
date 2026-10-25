/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part2
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVertexSquareSite_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexSquareSite R) := by
  intro x y hxy
  have hpoint := fkRectSquareSiteOfPair_injective hxy
  have hlift := fkRectSquareDevelopPoint_injective hpoint
  apply Prod.ext
  · apply Fin.ext
    have hxInt : (x.1.val : Int) = y.1.val := by
      simpa only [Prod.fst] using congrArg (fun z => z.1) hlift
    exact_mod_cast hxInt
  · apply Fin.ext
    have hyInt : (x.2.val : Int) = y.2.val := by
      simpa only [Prod.snd] using congrArg (fun z => z.2) hlift
    exact_mod_cast hyInt


theorem fkRectSquareAxisStep_iff_hypercubicAdj (p q : Int × Int) :
    FKRectSquareAxisStep p q ↔
      (hypercubicLattice 2).Adj
        (fkRectSquareSiteOfPair p) (fkRectSquareSiteOfPair q) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [fkRectSquareSiteOfPair_zero, fkRectSquareSiteOfPair_one]
  constructor
  · rintro (h | h | h | h)
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 1 := by omega
      have hpq1 : p.2 - q.2 = 0 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 0 := by omega
      have hpq1 : p.2 - q.2 = -1 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = -1 := by omega
      have hpq1 : p.2 - q.2 = 0 := by omega
      rw [hpq0, hpq1]
      norm_num
    · have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      simp only [Prod.fst_sub, Prod.snd_sub] at h0 h1
      have hpq0 : p.1 - q.1 = 0 := by omega
      have hpq1 : p.2 - q.2 = 1 := by omega
      rw [hpq0, hpq1]
      norm_num
  · intro h
    have habs :
        (p.1 - q.1).natAbs = 0 ∧ (p.2 - q.2).natAbs = 1 ∨
        (p.1 - q.1).natAbs = 1 ∧ (p.2 - q.2).natAbs = 0 := by
      omega
    rcases habs with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · have heq0 : p.1 = q.1 := by
        have := Int.natAbs_eq_zero.mp h0
        omega
      have hone : p.2 - q.2 = 1 ∨ p.2 - q.2 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h1)
      rcases hone with hone | hone
      · right; right; right
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
      · right; left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
    · have heq1 : p.2 = q.2 := by
        have := Int.natAbs_eq_zero.mp h1
        omega
      have hone : p.1 - q.1 = 1 ∨ p.1 - q.1 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h0)
      rcases hone with hone | hone
      · left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega
      · right; right; left
        apply Prod.ext <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> omega

@[simp] theorem mem_fkRectHorizontalCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectHorizontalCutEdges R ↔ a.2.2.val = 0 := by
  classical
  rcases a with ⟨b, x, y⟩
  unfold fkRectHorizontalCutEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨b', x'⟩, _, h⟩
    exact congrArg (fun e => e.2.2.val) h.symm
  · intro hy
    refine ⟨(b, x), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        simpa using hy.symm

@[simp] theorem mem_fkRectVerticalCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectVerticalCutEdges R ↔
      a.1 = false ∧ a.2.1.val = 0 := by
  classical
  rcases a with ⟨b, x, y⟩
  unfold fkRectVerticalCutEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y', _, h⟩
    constructor
    · exact congrArg (fun e => e.1) h.symm
    · exact congrArg (fun e => e.2.1.val) h.symm
  · rintro ⟨hb, hx⟩
    refine ⟨y, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · simpa using hb.symm
    · apply Prod.ext
      · apply Fin.ext
        simpa using hx.symm
      · rfl

@[simp] theorem mem_fkRectTorusCutEdges_iff
    (R : FKRectTorus) (a : R.EdgeIndex) :
    a ∈ fkRectTorusCutEdges R ↔
      a.2.2.val = 0 ∨ (a.1 = false ∧ a.2.1.val = 0) := by
  simp [fkRectTorusCutEdges]


theorem fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).1 =
      fkRectVertexSquarePoint R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).1) := by
  rcases a with ⟨b, x, y⟩
  rw [mem_fkRectTorusCutEdges_iff] at ha
  push Not at ha
  rcases ha with ⟨hy, hb⟩
  cases b
  · have hx : x.val ≠ 0 := hb rfl
    have hcastx : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    by_cases heven : Even y.val <;>
      simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
        fkRectVertexSquarePoint, fkRectCyclicPred_val,
        heven, hx, hcastx]
  · simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectVertexSquarePoint]

theorem fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂
    (R : FKRectTorus) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R a).2 =
      fkRectVertexSquarePoint R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R a).2) := by
  rcases a with ⟨b, x, y⟩
  rw [mem_fkRectTorusCutEdges_iff] at ha
  push Not at ha
  rcases ha with ⟨hy, hb⟩
  have hy0 : y.val ≠ 0 := by simpa using hy
  have hcasty : ((y.val - 1 : Nat) : Int) = (y.val : Int) - 1 := by
    omega
  cases b
  · have hx : x.val ≠ 0 := hb rfl
    have hcastx : ((x.val - 1 : Nat) : Int) = (x.val : Int) - 1 := by
      omega
    by_cases heven : Even y.val <;>
      simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
        fkRectVertexSquarePoint, fkRectCyclicPred_val,
        heven, hx, hy, hcastx, hcasty]
  · simp [fkRectLiftedIndexedEdgeEnds, fkRectLiftedVertex,
      fkRectVertexSquarePoint, fkRectCyclicPred_val, hy, hcasty]


theorem fkRectCutGraph_adj_imp_hypercubicAdj
    (R : FKRectTorus) {x y : R.Vertex}
    (hxy : (fkRectCutGraph R).Adj x y) :
    (hypercubicLattice 2).Adj
      (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
  obtain ⟨htorus, hcut⟩ := (fkRectCutGraph_adj_iff R x y).mp hxy
  obtain ⟨a, hedge⟩ := htorus
  have ha : a ∉ fkRectTorusCutEdges R := by
    intro ha
    apply hcut
    rw [← hedge]
    exact (mem_fkRectTorusCutGraphEdges R a).2 ha
  let p := (fkRectLiftedIndexedEdgeEnds R a).1
  let q := (fkRectLiftedIndexedEdgeEnds R a).2
  have hpair :
      s(fkRectLiftedVertex R p, fkRectLiftedVertex R q) = s(x, y) := by
    exact (fkRectLiftedIndexedEdgeEnds_project R a).symm.trans hedge
  have hstep := fkRectLiftedIndexedEdgeEnds_squareStep R a
  have haxis : FKRectSquareAxisStep
      (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) :=
    hstep.elim Or.inl (fun h => Or.inr (Or.inl h))
  have hp := fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut
    R a ha
  have hq := fkRectLiftedIndexedEdgeEnds_develop_eq_vertexPoint_of_not_cut₂
    R a ha
  change fkRectSquareDevelopPoint p = _ at hp
  change fkRectSquareDevelopPoint q = _ at hq
  rw [hp, hq] at haxis
  have hadj :=
    (fkRectSquareAxisStep_iff_hypercubicAdj _ _).mp haxis
  rcases Sym2.eq_iff.mp hpair with horient | horient
  · rw [horient.1, horient.2] at hadj
    simpa only [fkRectVertexSquareSite] using hadj
  · rw [horient.1, horient.2] at hadj
    simpa only [fkRectVertexSquareSite] using hadj.symm

theorem fkRectSquareDownStep_imp_cutGraph_adj
    (R : FKRectTorus) (x y : R.Vertex)
    (hstep :
      fkRectSquareDevelopPoint (y.1.val, y.2.val) -
          fkRectSquareDevelopPoint (x.1.val, x.2.val) = (-1, 0) ∨
      fkRectSquareDevelopPoint (y.1.val, y.2.val) -
          fkRectSquareDevelopPoint (x.1.val, x.2.val) = (0, 1)) :
    (fkRectCutGraph R).Adj x y := by
  let px : Int × Int := (x.1.val, x.2.val)
  let py : Int × Int := (y.1.val, y.2.val)
  have hrowRecoverX := fkRectSquareDevelopPoint_fst_sub_snd px
  have hrowRecoverY := fkRectSquareDevelopPoint_fst_sub_snd py
  have hcolRecoverX := fkRectSquareDevelopPoint_snd_add_rowHalf px
  have hcolRecoverY := fkRectSquareDevelopPoint_snd_add_rowHalf py
  rcases hstep with hstep | hstep
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    have hrow : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [px, py] at hrowRecoverX hrowRecoverY
      omega
    have hxrow0 : x.2.val ≠ 0 := by
      intro hx0
      have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
      simp only [hx0, Nat.cast_zero] at hrow
      omega
    have hpredRow :
        SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp only [if_neg hxrow0]
      omega
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hxrow : (x.2.val : Int) = 2 * (k : Int) := by
        have hkInt : (x.2.val : Int) = (k : Int) + k := by
          exact_mod_cast hk
        omega
      have hyrow : (y.2.val : Int) = 2 * (k : Int) - 1 := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) - 1 := by
        rw [hyrow]
        omega
      have hcol : (y.1.val : Int) = (x.1.val : Int) - 1 := by
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        omega
      have hxcol0 : x.1.val ≠ 0 := by
        intro hx0
        have hyNonneg : (0 : Int) ≤ y.1.val := by positivity
        simp only [hx0, Nat.cast_zero] at hcol
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos x.1 = y.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg hxcol0]
        omega
      let a : R.EdgeIndex := (false, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
          ↓reduceIte, hevenX]
        rw [hpredCol, hpredRow]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0, hxcol0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hxrow : (x.2.val : Int) = 2 * (k : Int) + 1 := by
        exact_mod_cast hk
      have hyrow : (y.2.val : Int) = 2 * (k : Int) := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) := by
        rw [hyrow]
        omega
      have hcol : y.1 = x.1 := by
        apply Fin.ext
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        exact_mod_cast (show (y.1.val : Int) = x.1.val by omega)
      let a : R.EdgeIndex := (true, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, ↓reduceIte]
        rw [hpredRow]
        rw [show (x.1, y.2) = y by exact Prod.ext hcol.symm rfl]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
  · have hu := congrArg Prod.fst hstep
    have hv := congrArg Prod.snd hstep
    simp only [Prod.fst_sub, Prod.snd_sub] at hu hv
    have hrow : (y.2.val : Int) = (x.2.val : Int) - 1 := by
      dsimp [px, py] at hrowRecoverX hrowRecoverY
      omega
    have hxrow0 : x.2.val ≠ 0 := by
      intro hx0
      have hyNonneg : (0 : Int) ≤ y.2.val := by positivity
      simp only [hx0, Nat.cast_zero] at hrow
      omega
    have hpredRow :
        SixVertexArrows.cyclicPred R.height_pos x.2 = y.2 := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      simp only [if_neg hxrow0]
      omega
    by_cases heven : Even x.2.val
    · obtain ⟨k, hk⟩ := heven
      have hevenX : Even x.2.val := ⟨k, hk⟩
      have hxrow : (x.2.val : Int) = 2 * (k : Int) := by
        have hkInt : (x.2.val : Int) = (k : Int) + k := by
          exact_mod_cast hk
        omega
      have hyrow : (y.2.val : Int) = 2 * (k : Int) - 1 := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) - 1 := by
        rw [hyrow]
        omega
      have hcol : y.1 = x.1 := by
        apply Fin.ext
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        exact_mod_cast (show (y.1.val : Int) = x.1.val by omega)
      let a : R.EdgeIndex := (true, x)
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, ↓reduceIte]
        rw [hpredRow]
        rw [show (x.1, y.2) = y by exact Prod.ext hcol.symm rfl]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩
    · have hodd : Odd x.2.val := Nat.not_even_iff_odd.mp heven
      obtain ⟨k, hk⟩ := hodd
      have hxrow : (x.2.val : Int) = 2 * (k : Int) + 1 := by
        exact_mod_cast hk
      have hyrow : (y.2.val : Int) = 2 * (k : Int) := by
        omega
      have hxhalf : (x.2.val : Int) / 2 = (k : Int) := by
        rw [hxrow]
        omega
      have hyhalf : (y.2.val : Int) / 2 = (k : Int) := by
        rw [hyrow]
        omega
      have hcol : (y.1.val : Int) = (x.1.val : Int) + 1 := by
        dsimp [px, py] at hcolRecoverX hcolRecoverY
        rw [hxhalf] at hcolRecoverX
        rw [hyhalf] at hcolRecoverY
        omega
      have hycol0 : y.1.val ≠ 0 := by
        intro hy0
        have hxNonneg : (0 : Int) ≤ x.1.val := by positivity
        simp only [hy0, Nat.cast_zero] at hcol
        omega
      have hpredCol :
          SixVertexArrows.cyclicPred R.width_pos y.1 = x.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        simp only [if_neg hycol0]
        omega
      let a : R.EdgeIndex := (false, (y.1, x.2))
      have hedge : fkRectTorusIndexedEdge R a = s(x, y) := by
        dsimp [a]
        simp only [fkRectTorusIndexedEdge, Bool.false_eq_true,
          ↓reduceIte, heven]
        rw [hpredCol, hpredRow]
      have ha : a ∉ fkRectTorusCutEdges R := by
        rw [mem_fkRectTorusCutEdges_iff]
        simp [a, hxrow0, hycol0]
      apply (fkRectCutGraph_adj_iff R x y).mpr
      exact ⟨⟨a, hedge⟩, by
        rw [← hedge, mem_fkRectTorusCutGraphEdges]
        exact ha⟩


theorem fkRectCutGraph_adj_iff_hypercubicAdj
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectCutGraph R).Adj x y ↔
      (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R x) (fkRectVertexSquareSite R y) := by
  constructor
  · exact fkRectCutGraph_adj_imp_hypercubicAdj R
  · intro hxy
    have haxis := (fkRectSquareAxisStep_iff_hypercubicAdj
      (fkRectVertexSquarePoint R x)
      (fkRectVertexSquarePoint R y)).mpr (by
        simpa only [fkRectVertexSquareSite] using hxy)
    rcases haxis with h | h | h | h
    · exact fkRectSquareDownStep_imp_cutGraph_adj R x y (Or.inl h)
    · exact fkRectSquareDownStep_imp_cutGraph_adj R x y (Or.inr h)
    · apply (fkRectCutGraph R).symm
      apply fkRectSquareDownStep_imp_cutGraph_adj R y x
      left
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [fkRectVertexSquarePoint, Prod.fst_sub,
          Prod.snd_sub] at h' h'' ⊢ <;>
        omega
    · apply (fkRectCutGraph R).symm
      apply fkRectSquareDownStep_imp_cutGraph_adj R y x
      right
      apply Prod.ext <;>
        have h' := congrArg Prod.fst h <;>
        have h'' := congrArg Prod.snd h <;>
        simp only [fkRectVertexSquarePoint, Prod.fst_sub,
          Prod.snd_sub] at h' h'' ⊢ <;>
        omega


theorem fkRectVertexSquareSite_mem_box
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVertexSquareSite R x ∈
      box 2 (R.width + R.height) := by
  intro i
  fin_cases i
  · simp only [fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint]
    have hu0 : (0 : Int) ≤
        (x.1.val : Int) + ((x.2.val : Int) + 1) / 2 := by
      positivity
    have huCast :
        (((x.1.val : Int) + ((x.2.val : Int) + 1) / 2).natAbs : Int) =
          (x.1.val : Int) + ((x.2.val : Int) + 1) / 2 :=
      Int.natAbs_of_nonneg hu0
    have hInt :
        (((x.1.val : Int) + ((x.2.val : Int) + 1) / 2).natAbs : Int) ≤
          (R.width + R.height : Nat) := by
      rw [huCast]
      have hx := x.1.isLt
      have hy := x.2.isLt
      omega
    exact_mod_cast hInt
  · simp only [fkRectVertexSquareSite, fkRectVertexSquarePoint,
      fkRectSquareSiteOfPair, fkRectSquareDevelopPoint]
    calc
      ((x.1.val : Int) - (x.2.val : Int) / 2).natAbs ≤
          (x.1.val : Int).natAbs +
            ((x.2.val : Int) / 2).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ R.width + R.height := by
        have hxCast : ((x.1.val : Int).natAbs : Int) = x.1.val :=
          Int.natAbs_of_nonneg (by positivity)
        have hyCast : (((x.2.val : Int) / 2).natAbs : Int) =
            (x.2.val : Int) / 2 :=
          Int.natAbs_of_nonneg (by positivity)
        have hInt :
            ((x.1.val : Int).natAbs : Int) +
                (((x.2.val : Int) / 2).natAbs : Int) ≤
              (R.width + R.height : Nat) := by
          rw [hxCast, hyCast]
          have hx := x.1.isLt
          have hy := x.2.isLt
          omega
        exact_mod_cast hInt


end
end StatMech.FrontierD
