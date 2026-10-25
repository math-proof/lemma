/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Structure.StatisticalMechanics.Code.FrontierA.SurfaceKacWardLocalGeometry
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

theorem SurfaceLocalSpinorGeometry.path_phase_sq_mul_direction
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (geometry : SurfaceLocalSpinorGeometry g G)
    {N : Nat} (path : Fin (N + 1) -> G.Dart)
    (hvalid : forall j : Fin N,
      G.DartAdj (path j.castSucc) (path j.succ) /\
        (path j.castSucc).edge ≠ (path j.succ).edge) :
    (∏ j : Fin N, geometry.phase
        (path j.castSucc) (path j.succ)) ^ 2 * geometry.direction (path 0) =
      geometry.direction (path (Fin.last N)) := by
  classical
  let phase : Fin N -> Complex := fun j =>
    geometry.phase (path j.castSucc) (path j.succ)
  let direction : Fin (N + 1) -> Complex := fun j => geometry.direction (path j)
  let prefixProd : Complex := ∏ j : Fin N, direction j.castSucc
  let suffixProd : Complex := ∏ j : Fin N, direction j.succ
  have hprod : (∏ j : Fin N, phase j) ^ 2 * prefixProd = suffixProd := by
    calc
      (∏ j : Fin N, phase j) ^ 2 * prefixProd =
          (∏ j : Fin N, phase j ^ 2) *
            ∏ j : Fin N, direction j.castSucc := by
              rw [Finset.prod_pow]
      _ = ∏ j : Fin N, phase j ^ 2 * direction j.castSucc := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ j : Fin N, direction j.succ := by
        apply Finset.prod_congr rfl
        intro j _
        exact geometry.phase_sq_transport _ _ (hvalid j).1 (hvalid j).2
  have hprefix_ne : prefixProd ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact geometry.direction_ne_zero _
  have hsuffix_eq : suffixProd =
      prefixProd * geometry.direction (path (Fin.last N)) /
        geometry.direction (path 0) := by
    have hfullCast := Fin.prod_univ_castSucc direction
    have hfullSucc := Fin.prod_univ_succ direction
    have hzero := geometry.direction_ne_zero (path 0)
    apply (mul_left_cancel₀ hzero)
    field_simp
    rw [← hfullSucc, ← hfullCast]
  change (∏ j : Fin N, phase j) ^ 2 * direction 0 =
    direction (Fin.last N)
  have hzero : direction 0 ≠ 0 := geometry.direction_ne_zero (path 0)
  apply (mul_left_cancel₀ hprefix_ne)
  calc
    prefixProd * ((∏ j : Fin N, phase j) ^ 2 * direction 0) =
        ((∏ j : Fin N, phase j) ^ 2 * prefixProd) * direction 0 := by ring
    _ = suffixProd * direction 0 := by rw [hprod]
    _ = (prefixProd * direction (Fin.last N) / direction 0) *
        direction 0 := by rw [hsuffix_eq]
    _ = prefixProd * direction (Fin.last N) := by field_simp


theorem SurfaceLocalSpinorGeometry.path_phase_sq
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (geometry : SurfaceLocalSpinorGeometry g G) :
    forall {N : Nat} (path : Fin (N + 1) -> G.Dart),
      path (Fin.last N) = (path 0).symm ->
      (forall j : Fin N,
        G.DartAdj (path j.castSucc) (path j.succ) /\
          (path j.castSucc).edge ≠ (path j.succ).edge) ->
      (∏ j : Fin N,
        geometry.phase (path j.castSucc) (path j.succ)) ^ 2 = -1 := by
  intro N path hend hvalid
  have htel := geometry.path_phase_sq_mul_direction path hvalid
  rw [hend, geometry.direction_reverse] at htel
  have hne := geometry.direction_ne_zero (path 0)
  apply (mul_right_cancel₀ hne)
  simpa only [neg_mul, one_mul] using htel


theorem SurfaceLocalSpinorGeometry.closed_phase_sq
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (geometry : SurfaceLocalSpinorGeometry g G) :
    forall {n : Nat} [NeZero n] (loop : Fin n -> G.Dart),
      (forall k : Fin n,
        G.DartAdj (loop k) (loop (k + 1)) /\
          (loop k).edge ≠ (loop (k + 1)).edge) ->
      (∏ k, geometry.phase (loop k) (loop (k + 1))) ^ 2 = 1 := by
  classical
  intro n hn loop hvalid
  let phase : Fin n -> Complex := fun k =>
    geometry.phase (loop k) (loop (k + 1))
  let direction : Fin n -> Complex := fun k => geometry.direction (loop k)
  have hprod : (∏ k : Fin n, phase k) ^ 2 * (∏ k : Fin n, direction k) =
      ∏ k : Fin n, direction (k + 1) := by
    calc
      (∏ k : Fin n, phase k) ^ 2 * (∏ k : Fin n, direction k) =
          (∏ k : Fin n, phase k ^ 2) * ∏ k : Fin n, direction k := by
            rw [Finset.prod_pow]
      _ = ∏ k : Fin n, phase k ^ 2 * direction k := by
        rw [Finset.prod_mul_distrib]
      _ = ∏ k : Fin n, direction (k + 1) := by
        apply Finset.prod_congr rfl
        intro k _
        exact geometry.phase_sq_transport _ _ (hvalid k).1 (hvalid k).2
  have hreindex : (∏ k : Fin n, direction (k + 1)) =
      ∏ k : Fin n, direction k := by
    exact Equiv.prod_comp (Equiv.addRight (1 : Fin n)) direction
  rw [hreindex] at hprod
  have hdirection : (∏ k : Fin n, direction k) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact geometry.direction_ne_zero _
  change (∏ k : Fin n, phase k) ^ 2 = 1
  apply mul_right_cancel₀ hdirection
  simpa only [one_mul] using hprod


theorem SurfaceLocalSpinorGeometry.intersection_formula
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (geometry : SurfaceLocalSpinorGeometry g G) (F K : Finset (Sym2 V)) :
    surfaceIntersection
        (surfaceSubgraphHomology geometry.edgeClass F)
        (surfaceSubgraphHomology geometry.edgeClass K) =
      ∑ edge ∈ F, ∑ other ∈ K,
        surfaceIntersection (geometry.edgeClass edge)
          (geometry.edgeClass other) :=
  surfaceIntersection_subgraphHomology_eq_doubleSum geometry.edgeClass F K


end StatMech.FrontierA
