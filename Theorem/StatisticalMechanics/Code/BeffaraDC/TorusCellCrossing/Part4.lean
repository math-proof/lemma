/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem torusCellCrossing_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellCrossing L (torusHorizontalEdge L x y) =
      torusVerticalEdge L x (y - 1) := by
  have hcode : (torusEdgeCodeEquiv L).symm
      (torusHorizontalEdge L x y) = ((x, y), .horizontal) := by
    apply (torusEdgeCodeEquiv L).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  change torusEdgeCodeEquiv L
      (torusCellCrossingCode L
        ((torusEdgeCodeEquiv L).symm (torusHorizontalEdge L x y))) = _
  rw [hcode]
  rfl

@[simp] theorem torusCellCrossing_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    torusCellCrossing L (torusVerticalEdge L x y) =
      torusHorizontalEdge L (x - 1) y := by
  have hcode : (torusEdgeCodeEquiv L).symm
      (torusVerticalEdge L x y) = ((x, y), .vertical) := by
    apply (torusEdgeCodeEquiv L).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  change torusEdgeCodeEquiv L
      (torusCellCrossingCode L
        ((torusEdgeCodeEquiv L).symm (torusVerticalEdge L x y))) = _
  rw [hcode]
  rfl

@[simp] theorem torusCellCrossing_horizontal_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusHorizontalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x, y - 1), (x, y)) := by
  rw [torusCellCrossing_horizontal, torusVerticalEdge_val]
  simp

@[simp] theorem torusCellCrossing_vertical_val
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L (torusVerticalEdge L x y) :
        Sym2 (ZMod L × ZMod L)) =
      s((x - 1, y), (x, y)) := by
  rw [torusCellCrossing_vertical, torusHorizontalEdge_val]
  simp


theorem torusCellCrossing_of_reversed_horizontal
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x + 1, y), (x, y))) :
    torusCellCrossing L e = torusVerticalEdge L x (y - 1) := by
  have heq : e = torusHorizontalEdge L x y := by
    apply Subtype.ext
    rw [he, torusHorizontalEdge_orientation_independent]
  rw [heq, torusCellCrossing_horizontal]


theorem torusCellCrossing_of_reversed_vertical
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) (x y : ZMod L)
    (he : (e : Sym2 (ZMod L × ZMod L)) =
      s((x, y + 1), (x, y))) :
    torusCellCrossing L e = torusHorizontalEdge L (x - 1) y := by
  have heq : e = torusVerticalEdge L x y := by
    apply Subtype.ext
    rw [he, torusVerticalEdge_orientation_independent]
  rw [heq, torusCellCrossing_vertical]

@[simp] theorem torusCellCrossing_symm_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusHorizontalEdge L x y) =
      torusVerticalEdge L (x + 1) y := by
  apply (torusCellCrossing L).injective
  simp

@[simp] theorem torusCellCrossing_symm_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusCellCrossing L).symm (torusVerticalEdge L x y) =
      torusHorizontalEdge L x (y + 1) := by
  apply (torusCellCrossing L).injective
  simp


theorem torusCellCrossing_mem_edgeFinset
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L e : Sym2 (ZMod L × ZMod L)) ∈
      (onsTorusGraph L).edgeFinset :=
  (torusCellCrossing L e).2

theorem torusCellCrossing_injective
    (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusCellCrossing L) :=
  (torusCellCrossing L).injective

theorem torusCellCrossing_surjective
    (L : ℕ) [Fact (2 < L)] :
    Function.Surjective (torusCellCrossing L) :=
  (torusCellCrossing L).surjective

@[simp] theorem torusCellCrossing_symm_apply_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    (torusCellCrossing L).symm (torusCellCrossing L e) = e :=
  (torusCellCrossing L).symm_apply_apply e

@[simp] theorem torusCellCrossing_apply_symm_apply
    (L : ℕ) [Fact (2 < L)] (e : TorusAmbientEdge L) :
    torusCellCrossing L ((torusCellCrossing L).symm e) = e :=
  (torusCellCrossing L).apply_symm_apply e

end StatMech.BeffaraDC
