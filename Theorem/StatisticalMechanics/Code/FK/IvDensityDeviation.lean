/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityDeviationFull.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem ivd_innerEdgeLE_refl (n : ℕ) (eb : Sym2 (boxVerts d n)) :
    innerEdgeLE d (le_refl n) eb = eb := by
  unfold innerEdgeLE boxVertInclLE
  rw [show (fun x : boxVerts d n =>
        (⟨(x : Site d), box_mono d (le_refl n) x.2⟩ : boxVerts d n)) = id by funext x; rfl]
  rw [Sym2.map_id]; rfl


theorem ivd_freeMeanOpenCount_le (n : ℕ) {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a) :
    fkMeanOpenCount (boxGraph d n) p 2 ≤ a * ((boxGraph d n).edgeFinset.card : ℝ) := by
  rw [fkMeanOpenCount_eq_sum_marginals]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, edgeMarginalOpen (boxGraph d n) p 2 e
      = ∑ e ∈ (boxGraph d n).edgeFinset, edgeMargProb (fkProb (boxGraph d n) p 2) e :=
        Finset.sum_congr rfl fun e _ => (edgeMargProb_fkProb (boxGraph d n) p 2 e).symm
    _ ≤ ∑ e ∈ (boxGraph d n).edgeFinset, a := by
        refine Finset.sum_le_sum fun e he => ?_
        have h1 := dfi_free_per_edge_le n n (le_refl n) e hp hp1
        rw [ivd_innerEdgeLE_refl n e] at h1
        rw [← hhom e he]; exact h1
    _ = a * ((boxGraph d n).edgeFinset.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


theorem ivd_wiredMeanOpenCount_eq_sum_marginals (n : ℕ) (p : ℝ) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
        (chOpenCount (boxGraph d n) ω : ℝ)
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω)
      = ∑ e ∈ (boxGraph d n).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
  have hexp : ∀ ω : ConfigSpace (Sym2 (boxVerts d n)),
      (chOpenCount (boxGraph d n) ω : ℝ)
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω
        = ∑ e ∈ (boxGraph d n).edgeFinset,
            (if ω e = true then wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω else 0) := by
    intro ω
    rw [chOpenCount_eq_sum_indicator (boxGraph d n) ω, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by split <;> ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold edgeMargProb
  exact (Finset.sum_congr rfl fun ω _ => by split <;> simp_all)


theorem ivd_wiredMeanOpenCount_ge (n : ℕ) {p b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b) :
    b * ((boxGraph d n).edgeFinset.card : ℝ)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (chOpenCount (boxGraph d n) ω : ℝ)
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  rw [ivd_wiredMeanOpenCount_eq_sum_marginals]
  calc b * ((boxGraph d n).edgeFinset.card : ℝ)
      = ∑ _e ∈ (boxGraph d n).edgeFinset, b := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ e ∈ (boxGraph d n).edgeFinset,
          edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) e := by
        refine Finset.sum_le_sum fun e he => ?_
        have h1 := dfi_wired_per_edge_ge n n (le_refl n) e hp hp1
        rw [ivd_innerEdgeLE_refl n e] at h1
        rw [← hhom e he]; exact h1


end FK
end StatMech
