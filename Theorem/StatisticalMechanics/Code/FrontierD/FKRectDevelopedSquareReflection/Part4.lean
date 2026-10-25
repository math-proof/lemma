/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquareReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part4
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_apply
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectDevelopedReflectionEdgeEquiv R center a =
      (a.1, (a.2.1, finitePeriodicSucc R.height_pos
        (fkRectRowReflection R center a.2.2))) :=
  rfl


theorem fkRectTorusIndexedEdge_developedReflection
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R
        (fkRectDevelopedReflectionEdgeEquiv R center a) =
      Sym2.map (fkRectDevelopedReflectionVertexEquiv R center)
        (fkRectTorusIndexedEdge R a) := by
  rcases a with ⟨b, x, y⟩
  cases b
  · have hrefEven :
        Even (fkRectRowReflection R center y).val ↔ Even y.val :=
      fkRectRowReflection_even_iff R center y
    have hsuccEven :
        Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val ↔ ¬ Even y.val := by
      rw [even_finitePeriodicSucc_iff, hrefEven]
    by_cases hy : Even y.val
    · have hsy : ¬ Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val := by
        simpa [hsuccEven] using hy
      simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy, if_true,
        hsy, fkRectDevelopedReflectionVertexEquiv_apply, Sym2.map_pair_eq]
      rw [fkRectRowReflection_cyclicPred,
        fkRectRowReflection_succ_cyclicPred]
      exact Sym2.eq_swap
    · have hsy : Even (finitePeriodicSucc R.height_pos
          (fkRectRowReflection R center y)).val := hsuccEven.mpr hy
      simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
        fkRectTorusIndexedEdge, Bool.false_eq_true, if_false, hy,
        hsy, if_true, fkRectDevelopedReflectionVertexEquiv_apply,
        Sym2.map_pair_eq]
      rw [fkRectRowReflection_cyclicPred,
        fkRectRowReflection_succ_cyclicPred]
      exact Sym2.eq_swap
  · simp only [fkRectDevelopedReflectionEdgeEquiv_apply,
      fkRectTorusIndexedEdge, if_true,
      fkRectDevelopedReflectionVertexEquiv_apply, Sym2.map_pair_eq]
    rw [fkRectRowReflection_cyclicPred,
      fkRectRowReflection_succ_cyclicPred]
    exact Sym2.eq_swap


theorem fkRectTorusGraph_adj_developedReflection
    (R : FKRectTorus) (center : Nat) (x y : R.Vertex) :
    (fkRectTorusGraph R).Adj
        (fkRectDevelopedReflectionVertexEquiv R center x)
        (fkRectDevelopedReflectionVertexEquiv R center y) ↔
      (fkRectTorusGraph R).Adj x y := by
  constructor
  · rintro ⟨a, ha⟩
    let b := (fkRectDevelopedReflectionEdgeEquiv R center).symm a
    refine ⟨b, ?_⟩
    have href := fkRectTorusIndexedEdge_developedReflection R center b
    rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply a,
      ha] at href
    have hcomp :
        (fkRectDevelopedReflectionVertexEquiv R center) ∘
            (fkRectDevelopedReflectionVertexEquiv R center) = id := by
      funext v
      apply Prod.ext
      · rfl
      · exact fkRectRowReflection_involutive R center v.2
    have := congrArg
      (Sym2.map (fkRectDevelopedReflectionVertexEquiv R center)) href
    rw [Sym2.map_map, hcomp] at this
    have hxinv : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center x) = x :=
      congrFun hcomp x
    have hyinv : fkRectDevelopedReflectionVertexEquiv R center
        (fkRectDevelopedReflectionVertexEquiv R center y) = y :=
      congrFun hcomp y
    rw [Sym2.map_mk, hxinv, hyinv] at this
    simpa using this.symm
  · rintro ⟨a, ha⟩
    refine ⟨fkRectDevelopedReflectionEdgeEquiv R center a, ?_⟩
    rw [fkRectTorusIndexedEdge_developedReflection, ha]
    rfl

theorem fkRectDevelopedReflectionVertexEquiv_symm_apply
    (R : FKRectTorus) (center : Nat) (v : R.Vertex) :
    (fkRectDevelopedReflectionVertexEquiv R center).symm v =
      fkRectDevelopedReflectionVertexEquiv R center v := by
  apply (fkRectDevelopedReflectionVertexEquiv R center).injective
  rw [(fkRectDevelopedReflectionVertexEquiv R center).apply_symm_apply]
  apply Prod.ext
  · rfl
  · exact (fkRectRowReflection_involutive R center v.2).symm

theorem fkRectDevelopedReflectionEdgeEquiv_involutive
    (R : FKRectTorus) (center : Nat) :
    Function.Involutive (fkRectDevelopedReflectionEdgeEquiv R center) := by
  intro a
  apply fkRectTorusIndexedEdge_injective R
  rw [fkRectTorusIndexedEdge_developedReflection,
    fkRectTorusIndexedEdge_developedReflection, Sym2.map_map]
  have hcomp :
      (fkRectDevelopedReflectionVertexEquiv R center) ∘
          (fkRectDevelopedReflectionVertexEquiv R center) = id := by
    funext v
    apply Prod.ext
    · rfl
    · exact fkRectRowReflection_involutive R center v.2
  rw [hcomp]
  simp

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_twice
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    fkRectDevelopedReflectionEdgeEquiv R center
        (fkRectDevelopedReflectionEdgeEquiv R center a) = a :=
  fkRectDevelopedReflectionEdgeEquiv_involutive R center a

@[simp] theorem fkRectDevelopedReflectionEdgeEquiv_symm_apply
    (R : FKRectTorus) (center : Nat) (a : R.EdgeIndex) :
    (fkRectDevelopedReflectionEdgeEquiv R center).symm a =
      fkRectDevelopedReflectionEdgeEquiv R center a := by
  apply (fkRectDevelopedReflectionEdgeEquiv R center).injective
  rw [(fkRectDevelopedReflectionEdgeEquiv R center).apply_symm_apply,
    fkRectDevelopedReflectionEdgeEquiv_involutive R center a]


end
end StatMech.FrontierD
