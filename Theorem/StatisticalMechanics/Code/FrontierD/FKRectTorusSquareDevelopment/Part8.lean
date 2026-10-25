/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part8


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareRepresentativeVertex_developPoint
    (R : FKRectTorus) (p : Int × Int) :
    fkRectSquareRepresentativeVertex R (fkRectSquareDevelopPoint p) =
      fkRectLiftedVertex R p := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [fkRectSquareRepresentativeVertex, fkRectLiftedVertex,
      fkRectIntModFin]


theorem fkRectVertexSquareClass_representative
    (R : FKRectTorus) (z : Int × Int) :
    fkRectVertexSquareClass R (fkRectSquareRepresentativeVertex R z) =
      QuotientAddGroup.mk z := by
      let p := fkRectSquareUndevelopPoint z
      let x := fkRectSquareRepresentativeVertex R z
      let u : Int × Int :=
        (p.1 / (R.width : Int), p.2 / (R.height : Int))
      have hw : (R.width : Int) ≠ 0 := by
        exact_mod_cast (ne_of_gt R.width_pos)
      have hh : (R.height : Int) ≠ 0 := by
        exact_mod_cast (ne_of_gt R.height_pos)
      have hremWidth : ((p.1.natMod R.width : Nat) : Int) =
          p.1 % (R.width : Int) := by
        rw [Int.natMod, Int.natCast_toNat_eq_self]
        exact Int.emod_nonneg _ hw
      have hremHeight : ((p.2.natMod R.height : Nat) : Int) =
          p.2 % (R.height : Int) := by
        rw [Int.natMod, Int.natCast_toNat_eq_self]
        exact Int.emod_nonneg _ hh
      have hp :
          ((x.1.val : Int) + (R.width : Int) * u.1,
            (x.2.val : Int) + (R.height : Int) * u.2) = p := by
        apply Prod.ext
        · dsimp [x, fkRectSquareRepresentativeVertex, p, u]
          rw [hremWidth]
          exact Int.emod_add_ediv _ _
        · dsimp [x, fkRectSquareRepresentativeVertex, p, u]
          rw [hremHeight]
          exact Int.emod_add_ediv _ _
      have hperiod := fkRectSquareDevelopPoint_add_period R
        ((x.1.val : Int), (x.2.val : Int)) u
      have hdevelop : fkRectVertexSquarePoint R x +
          fkRectSquareDeckTranslation R u = z := by
        have hz : fkRectSquareDevelopPoint p = z := by
          dsimp [p]
          exact fkRectSquareDevelopPoint_undevelopPoint z
        rw [← hz, ← hp]
        dsimp [fkRectVertexSquarePoint]
        apply Prod.ext
        · have h := congrArg Prod.fst hperiod
          simp only [Prod.fst_sub, Prod.fst_add] at h ⊢
          omega
        · have h := congrArg Prod.snd hperiod
          simp only [Prod.snd_sub, Prod.snd_add] at h ⊢
          omega
      change QuotientAddGroup.mk (fkRectVertexSquarePoint R x) =
        QuotientAddGroup.mk z
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply (mem_fkRectSquareDeckLattice_iff R _).mpr
      refine ⟨-u, ?_⟩
      have hmap : fkRectSquareDeckTranslation R (-u) =
          -fkRectSquareDeckTranslation R u :=
        map_neg (fkRectSquareDeckHom R) u
      rw [hmap, ← hdevelop]
      abel


theorem fkRectVertexSquareClass_liftedVertex
    (R : FKRectTorus) (p : Int × Int) :
    fkRectVertexSquareClass R (fkRectLiftedVertex R p) =
      QuotientAddGroup.mk (fkRectSquareDevelopPoint p) := by
  rw [← fkRectSquareRepresentativeVertex_developPoint]
  exact fkRectVertexSquareClass_representative R
    (fkRectSquareDevelopPoint p)


theorem fkRectLiftedIndexedEdgeEnds_project
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectTorusIndexedEdge R e =
      s(fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1,
        fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) := by
  rcases e with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectLiftedVertex, hy]
    · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
        fkRectLiftedVertex, hy]
  · simp [fkRectTorusIndexedEdge, fkRectLiftedIndexedEdgeEnds,
      fkRectLiftedVertex]


theorem fkRectLiftedIndexedEdgeEnds_developedStep
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectDevelopedStep R
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1)
        (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) =
      (fkRectLiftedIndexedEdgeEnds R e).2 -
        (fkRectLiftedIndexedEdgeEnds R e).1 := by
  rcases e with ⟨b, x, y⟩
  cases b
  · by_cases hy : Even y.val
    · simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
        ↓reduceIte, hy, fkRectLiftedVertex, Prod.fst, Prod.snd,
        fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
      rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val,
        fkRectCyclicPred_val]
      by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
        simp [hx0, hy0] <;> omega
    · simp only [fkRectLiftedIndexedEdgeEnds, Bool.false_eq_true,
        ↓reduceIte, hy, fkRectLiftedVertex, Prod.fst, Prod.snd,
        fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
      rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_swap,
        fkRectHorizontalSeamIncrement_pred,
        fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val,
        fkRectCyclicPred_val]
      by_cases hx0 : x.val = 0 <;> by_cases hy0 : y.val = 0 <;>
        simp [hx0, hy0] <;> omega
  · simp only [fkRectLiftedIndexedEdgeEnds, ↓reduceIte,
      fkRectLiftedVertex, Prod.fst, Prod.snd,
      fkRectIntModFin_natCast, fkRectIntModFin_natCast_sub_one]
    rw [fkRectDevelopedStep, fkRectHorizontalSeamIncrement_same_fst,
      fkRectVerticalSeamIncrement_pred, fkRectCyclicPred_val]
    by_cases hy0 : y.val = 0 <;> simp [hy0] <;> omega


theorem fkRectIndexedEdge_squareLift
    (R : FKRectTorus) (e : R.EdgeIndex) :
    ∃ p q : Int × Int,
      fkRectTorusIndexedEdge R e =
        s(fkRectLiftedVertex R p, fkRectLiftedVertex R q) ∧
      fkRectVertexSquareClass R (fkRectLiftedVertex R p) =
        QuotientAddGroup.mk (fkRectSquareDevelopPoint p) ∧
      fkRectVertexSquareClass R (fkRectLiftedVertex R q) =
        QuotientAddGroup.mk (fkRectSquareDevelopPoint q) ∧
      fkRectDevelopedStep R (fkRectLiftedVertex R p)
          (fkRectLiftedVertex R q) = q - p ∧
      (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨
        fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) := by
  refine ⟨(fkRectLiftedIndexedEdgeEnds R e).1,
    (fkRectLiftedIndexedEdgeEnds R e).2,
    fkRectLiftedIndexedEdgeEnds_project R e,
    fkRectVertexSquareClass_liftedVertex R _,
    fkRectVertexSquareClass_liftedVertex R _,
    fkRectLiftedIndexedEdgeEnds_developedStep R e, ?_⟩
  exact fkRectLiftedIndexedEdgeEnds_squareStep R e


theorem fkRectLiftedVertex_eq_iff_exists_period
    (R : FKRectTorus) (p q : Int × Int) :
    fkRectLiftedVertex R p = fkRectLiftedVertex R q ↔
      ∃ u : Int × Int,
        p = (q.1 + (R.width : Int) * u.1,
          q.2 + (R.height : Int) * u.2) := by
  constructor
  · intro hpq
    have hclass :
        (QuotientAddGroup.mk (fkRectSquareDevelopPoint p) :
            FKRectSquareTorus R) =
          QuotientAddGroup.mk (fkRectSquareDevelopPoint q) := by
      rw [← fkRectVertexSquareClass_liftedVertex R p,
        ← fkRectVertexSquareClass_liftedVertex R q, hpq]
    have hmem : fkRectSquareDevelopPoint p -
        fkRectSquareDevelopPoint q ∈ fkRectSquareDeckLattice R :=
      QuotientAddGroup.eq_iff_sub_mem.mp hclass
    obtain ⟨u, hu⟩ :=
      (mem_fkRectSquareDeckLattice_iff R _).mp hmem
    have hdevelop : fkRectSquareDevelopPoint p =
        fkRectSquareDevelopPoint q + fkRectSquareDeckTranslation R u := by
      rw [hu]
      apply Prod.ext <;> simp <;> ring
    have hundevelop := congrArg fkRectSquareUndevelopPoint hdevelop
    rw [fkRectSquareUndevelopPoint_developPoint,
      fkRectSquareUndevelopPoint_add_deck,
      fkRectSquareUndevelopPoint_developPoint] at hundevelop
    exact ⟨u, hundevelop⟩
  · rintro ⟨u, rfl⟩
    apply fkRectVertexSquareClass_injective R
    rw [fkRectVertexSquareClass_liftedVertex,
      fkRectVertexSquareClass_liftedVertex]
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    apply (mem_fkRectSquareDeckLattice_iff R _).mpr
    refine ⟨u, ?_⟩
    exact (fkRectSquareDevelopPoint_add_period R q u).symm


end
end StatMech.FrontierD
