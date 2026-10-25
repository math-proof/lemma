/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Def.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem fkTI_signFlip_moves (d : ℕ) (j : Fin d) (x : Site d) (hx : x j ≠ 0) :
    (fkTI_signFlip d j).τ x ≠ x := by
  intro h
  have hj : (fkTI_signFlip d j).τ x j = x j := by rw [h]
  have hflip : (fkTI_signFlip d j).τ x j = -(x j) := by
    show (if j = j then -(x j) else x j) = -(x j)
    rw [if_pos rfl]
  rw [hflip] at hj
  omega


theorem fkTI_box_density_bound_wired_const (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB₀ : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB₀, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (EB₀.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  have hsum : (∑ eb ∈ EB₀, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB₀.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_wired N n hNn EB₀ hp hp1


theorem fkTI_box_density_bound_free_const (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB₀ : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB₀, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB₀.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB₀.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hsum : (∑ eb ∈ EB₀, freeEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB₀.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_free N n hNn EB₀ hp hp1

end FK
end StatMech
