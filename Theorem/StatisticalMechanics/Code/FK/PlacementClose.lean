/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PlacementClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.MultiEdgeDecay.Part4
open MeasureTheory Filter Topology SimpleGraph Set
open StatMech.ConfigSpace StatMech.Lattice
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.IsingFK

variable {d : ℕ}


theorem plc_relift_image (N₀ N : ℕ) (h : N₀ ≤ N) (t₀ : Finset (Sym2 (boxVerts d N₀))) :
    (t₀.image (innerEdgeLE d h)).image (edgeIncl d N) = t₀.image (edgeIncl d N₀) := by
  rw [Finset.image_image]
  refine Finset.image_congr fun eb _ => ?_
  exact med_edgeIncl_innerEdgeLE N₀ N h eb


theorem plc_common_box (g : Multiplicative (Site d)) (s : Finset (Sym2 (Site d))) :
    ∃ (N : ℕ) (t t' : Finset (Sym2 (boxVerts d N))),
      s = t.image (edgeIncl d N)
        ∧ s.image (fun e => g⁻¹ • e) = t'.image (edgeIncl d N) := by
  classical
  obtain ⟨N₁, t₁, hst₁⟩ := cdc_finset_in_box s
  obtain ⟨N₂, t₂, hst₂⟩ := cdc_finset_in_box (s.image (fun e => g⁻¹ • e))
  refine ⟨max N₁ N₂,
    t₁.image (innerEdgeLE d (le_max_left N₁ N₂)),
    t₂.image (innerEdgeLE d (le_max_right N₁ N₂)), ?_, ?_⟩
  · rw [hst₁, plc_relift_image N₁ (max N₁ N₂) (le_max_left N₁ N₂) t₁]
  · rw [hst₂, plc_relift_image N₂ (max N₁ N₂) (le_max_right N₁ N₂) t₂]


theorem plc_htrans_iff_centred_shift_wired (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} :
    (med_multiMassProb
          (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p 2)
          ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
        = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
            (t'.image (innerEdgeLE d hNm)))
      ↔ (med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
            (t.image (innerEdgeLE d hNm))
          = med_multiMassProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2)
              (t'.image (innerEdgeLE d hNm))) := by
  rw [← med_centred_eq_translated_wired m v (t.image (innerEdgeLE d hNm))]


theorem plc_htrans_iff_centred_shift_free (m : ℕ) (v : Site d) (N : ℕ) (hNm : N ≤ m)
    (t t' : Finset (Sym2 (boxVerts d N))) {p : ℝ} :
    (med_multiMassProb (fkProb (fvs_transBoxGraph d m v) p 2)
          ((t.image (innerEdgeLE d hNm)).image (Sym2.map (fvs_transEquiv d m v)))
        = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm)))
      ↔ (med_multiMassProb (fkProb (boxGraph d m) p 2) (t.image (innerEdgeLE d hNm))
          = med_multiMassProb (fkProb (boxGraph d m) p 2) (t'.image (innerEdgeLE d hNm))) := by
  rw [← med_centred_eq_translated_free m v (t.image (innerEdgeLE d hNm))]


end FK
end StatMech
