/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Def.StatisticalMechanics.Code.FK.DensityFiniteToInfinite
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem dfi_openEdgeCount_expect {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (μ : ConfigSpace (Sym2 V) → ℝ) :
    (∑ ω : ConfigSpace (Sym2 V), dfi_openEdgeCount E ω * μ ω)
      = ∑ e ∈ E, edgeMargProb μ e := by
  unfold dfi_openEdgeCount edgeMargProb
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_mul]


theorem dfi_boxVertInclLE_injective (d : ℕ) {N n : ℕ} (hNn : N ≤ n) :
    Function.Injective (boxVertInclLE d hNn) := by
  intro x y h
  apply Subtype.ext
  have : (boxVertInclLE d hNn x : Site d) = (boxVertInclLE d hNn y : Site d) :=
    congrArg Subtype.val h
  exact this


theorem dfi_innerEdgeLE_injective (d : ℕ) {N n : ℕ} (hNn : N ≤ n) :
    Function.Injective (innerEdgeLE d hNn) :=
  Sym2.map.injective (dfi_boxVertInclLE_injective d hNn)


theorem dfi_box_density_bound_wired (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [dfi_openEdgeCount_expect]
  rw [Finset.sum_image (fun a _ b _ h => dfi_innerEdgeLE_injective d hNn h)]
  exact Finset.sum_le_sum fun eb _ => dfi_wired_per_edge_ge N n hNn eb hp hp1


theorem dfi_box_density_bound_free (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ ∑ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p := by
  rw [dfi_openEdgeCount_expect]
  rw [Finset.sum_image (fun a _ b _ h => dfi_innerEdgeLE_injective d hNn h)]
  exact Finset.sum_le_sum fun eb _ => dfi_free_per_edge_le N n hNn eb hp hp1

end FK
end StatMech
