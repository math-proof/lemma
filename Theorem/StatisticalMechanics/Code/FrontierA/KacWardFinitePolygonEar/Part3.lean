/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part2


namespace StatMech.FrontierA

@[simp] theorem kwVectorPhasePath_nil :
    kwVectorPhasePath [] = 1 := rfl

@[simp] theorem kwVectorPhasePath_singleton (x : ℂ) :
    kwVectorPhasePath [x] = 1 := rfl

@[simp] theorem kwVectorPhasePath_cons_cons
    (x y : ℂ) (tail : List ℂ) :
    kwVectorPhasePath (x :: y :: tail) =
      kwVectorTurnPhase x y * kwVectorPhasePath (y :: tail) := rfl

@[simp] theorem kwVectorPhaseCycle_nil :
    kwVectorPhaseCycle [] = 1 := rfl

@[simp] theorem kwVectorPhaseCycle_cons (x : ℂ) (tail : List ℂ) :
    kwVectorPhaseCycle (x :: tail) =
      kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) x := rfl


theorem kwVectorPhasePath_mul_last_eq_zipWith
    (x closing : ℂ) (tail : List ℂ) :
    kwVectorPhasePath (x :: tail) *
        kwVectorTurnPhase ((x :: tail).getLastD x) closing =
      (List.zipWith kwVectorTurnPhase (x :: tail)
        (tail ++ [closing])).prod := by
  induction tail generalizing x with
  | nil => simp [kwVectorPhasePath]
  | cons y tail ih =>
      simp only [kwVectorPhasePath_cons_cons, List.getLastD_cons,
        List.cons_append, List.zipWith_cons_cons, List.prod_cons]
      have hih := ih y
      simp only [List.getLastD_cons] at hih
      rw [← hih]
      ring


theorem kwVectorPhaseCycle_eq_zipWith (edges : List ℂ) :
    kwVectorPhaseCycle edges =
      (List.zipWith kwVectorTurnPhase edges (edges.rotate 1)).prod := by
  rcases edges with _ | ⟨x, tail⟩
  · simp
  · cases tail with
    | nil => simp [kwVectorPhaseCycle, kwVectorPhasePath,
        kwVectorTurnPhase]
    | cons y tail =>
        rw [kwVectorPhaseCycle_cons,
          kwVectorPhasePath_mul_last_eq_zipWith x x (y :: tail),
          List.zipWith_rotate_one]
        simp


theorem kwVectorPhaseCycle_rotate (edges : List ℂ) (r : ℕ) :
    kwVectorPhaseCycle (edges.rotate r) = kwVectorPhaseCycle edges := by
  rw [kwVectorPhaseCycle_eq_zipWith, kwVectorPhaseCycle_eq_zipWith]
  have hrotate :
      List.zipWith kwVectorTurnPhase (edges.rotate r)
          ((edges.rotate r).rotate 1) =
        (List.zipWith kwVectorTurnPhase edges (edges.rotate 1)).rotate r := by
    rw [List.zipWith_rotate_distrib kwVectorTurnPhase edges
      (edges.rotate 1) r (by simp)]
    congr 1
    simp only [List.rotate_rotate]
    rw [Nat.add_comm]
  rw [hrotate]
  exact (List.rotate_perm _ _).prod_eq


theorem kwVectorPhaseCycle_ofFn {n : ℕ} [NeZero n]
    (edge : Fin n → ℂ) :
    kwVectorPhaseCycle (List.ofFn edge) =
      kwLoopPhaseProduct kwVectorTurnPhase edge := by
  rw [kwVectorPhaseCycle_eq_zipWith]
  unfold kwLoopPhaseProduct
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    rw [List.getElem_zipWith]
    simp only [List.getElem_ofFn]
    rw [List.getElem_rotate]
    simp only [List.length_ofFn, List.getElem_ofFn]
    congr 2
    apply Fin.ext
    rw [Fin.val_add]
    simp [Nat.add_mod]


theorem KWStraightLineEmbedding.vectorTurnPhase_eq_turnPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) :
    kwVectorTurnPhase
        (embedding.vertex dart.snd - embedding.vertex dart.fst)
        (embedding.vertex next.snd - embedding.vertex next.fst) =
      embedding.turnPhase dart next := by
  simpa only [kwVectorTurnPhase, kwAngleTurnPhase,
    kwPrincipalHalfAnglePhase] using
      embedding.principalPhase_eq_turnPhase dart next


theorem KWStraightLineEmbedding.vectorPhaseCycle_of_dartLoop
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    {n : ℕ} [NeZero n] (loop : Fin n → G.Dart) :
    kwVectorPhaseCycle (List.ofFn fun k ↦
        embedding.vertex (loop k).snd - embedding.vertex (loop k).fst) =
      kwLoopPhaseProduct embedding.turnPhase loop := by
  rw [kwVectorPhaseCycle_ofFn]
  unfold kwLoopPhaseProduct
  apply Finset.prod_congr rfl
  intro k _
  exact embedding.vectorTurnPhase_eq_turnPhase (loop k) (loop (k + 1))


theorem KWStraightLineEmbedding.incident_collinear_sameRay
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart)
    (hadj : dart.snd = next.fst)
    (houter : dart.fst ≠ next.snd)
    (hcol : Collinear ℝ
      ({embedding.vertex dart.fst, embedding.vertex dart.snd,
        embedding.vertex next.snd} : Set ℂ)) :
    SameRay ℝ
      (embedding.vertex dart.snd - embedding.vertex dart.fst)
      (embedding.vertex next.snd - embedding.vertex next.fst) := by
  have hAB : dart.fst ≠ dart.snd := dart.fst_ne_snd
  have hBC : dart.snd ≠ next.snd := by
    rw [hadj]
    exact next.fst_ne_snd
  rcases hcol.wbtw_or_wbtw_or_wbtw with hmid | hmid | hmid
  · simpa only [vsub_eq_sub, hadj] using hmid.sameRay_vsub
  · have hstrict : Sbtw ℝ (embedding.vertex dart.snd)
        (embedding.vertex next.snd) (embedding.vertex dart.fst) :=
      ⟨hmid, embedding.vertex_injective.ne hBC.symm,
        embedding.vertex_injective.ne houter.symm⟩
    exact (embedding.vertex_not_strictly_between dart.symm next.snd
      hBC.symm houter.symm hstrict).elim
  · have hstrict : Sbtw ℝ (embedding.vertex next.snd)
        (embedding.vertex dart.fst) (embedding.vertex dart.snd) :=
      ⟨hmid, embedding.vertex_injective.ne houter,
        embedding.vertex_injective.ne hAB⟩
    exact (embedding.vertex_not_strictly_between next.symm dart.fst
      houter (by simpa only [hadj] using hAB) (by simpa only [hadj] using hstrict)).elim


end StatMech.FrontierA
