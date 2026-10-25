/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.TranslationInvariance.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


@[simp] theorem BoxSym.lift_val (S : BoxSym d) (n : ℕ) (x : boxVerts d n) :
    (S.lift n x : Site d) = S.τ x.val := rfl


theorem BoxSym.lift_adj (S : BoxSym d) (n : ℕ) (x y : boxVerts d n) :
    (boxGraph d n).Adj (S.lift n x) (S.lift n y) ↔ (boxGraph d n).Adj x y := by
  rw [boxGraph, SimpleGraph.comap_adj, SimpleGraph.comap_adj]
  show (hypercubicLattice d).Adj (S.τ x.val) (S.τ y.val) ↔ _
  rw [S.adj]


theorem BoxSym.lift_boundary (S : BoxSym d) (n : ℕ) (x : boxVerts d n) :
    boxBoundary d n (S.lift n x) ↔ boxBoundary d n x := by
  unfold boxBoundary
  show S.τ x.val ∈ vertexBoundary d n ↔ x.val ∈ vertexBoundary d n
  simp only [mem_vertexBoundary, S.box_mem]


theorem BoxSym.lift_boxVertInclLE (S : BoxSym d) {N m : ℕ} (h : N ≤ m) (x : boxVerts d N) :
    S.lift m (boxVertInclLE d h x) = boxVertInclLE d h (S.lift N x) := by
  apply Subtype.ext
  show S.τ x.val = S.τ x.val
  rfl


theorem BoxSym.lift_innerEdgeLE (S : BoxSym d) {N m : ℕ} (h : N ≤ m) (eb : Sym2 (boxVerts d N)) :
    Sym2.map (S.lift m) (innerEdgeLE d h eb) = innerEdgeLE d h (Sym2.map (S.lift N) eb) := by
  unfold innerEdgeLE
  rw [Sym2.map_map, Sym2.map_map]
  apply Sym2.map_congr
  intro z _
  exact S.lift_boxVertInclLE h z


theorem fkTI_box_wired_edgeMarg_inv (S : BoxSym d) (m : ℕ) {p : ℝ} (e : Sym2 (boxVerts d m)) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (Sym2.map (S.lift m) e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) e :=
  fkTI_edgeMargProb_wiredFkProb_reCfg (boxGraph d m) (boxBoundary d m) (S.lift m)
    (S.lift_adj m) (S.lift_boundary m) p 2 e


theorem fkTI_box_free_edgeMarg_inv (S : BoxSym d) (m : ℕ) {p : ℝ} (e : Sym2 (boxVerts d m)) :
    edgeMargProb (fkProb (boxGraph d m) p 2) (Sym2.map (S.lift m) e)
      = edgeMargProb (fkProb (boxGraph d m) p 2) e :=
  fkTI_edgeMargProb_fkProb_reCfg (boxGraph d m) (S.lift m) (S.lift_adj m) p 2 e


theorem fkTI_wired_density_shift_inv (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  
  have hlim₁ := dfi_wired_density_eq_limit N eb hp hp1
  have hlim₂ := dfi_wired_density_eq_limit N (Sym2.map (S.lift N) eb) hp hp1
  refine tendsto_nhds_unique hlim₁ ?_
  refine hlim₂.congr (fun k => ?_)
  
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) eb,
    fkTI_box_wired_edgeMarg_inv S (N+k) (innerEdgeLE d (Nat.le_add_right N k) eb)]


theorem fkTI_free_density_shift_inv (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
  have hlim₁ := dfi_free_density_eq_limit N eb hp hp1
  have hlim₂ := dfi_free_density_eq_limit N (Sym2.map (S.lift N) eb) hp hp1
  refine tendsto_nhds_unique hlim₁ ?_
  refine hlim₂.congr (fun k => ?_)
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) eb,
    fkTI_box_free_edgeMarg_inv S (N+k) (innerEdgeLE d (Nat.le_add_right N k) eb)]


end FK
end StatMech
