/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part3
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_connectedContourCount_of_encoding {n : ℕ}
    (h : ∀ ℓ, ccb_ContourEncodingExists d n ℓ) :
    ConnectedContourCount d n := by
  intro ℓ
  obtain ⟨anchors, hcard, enc, hmaps, hinj⟩ := h ℓ
  have hcardfib : (ccb_contourFiber d n ℓ).card ≤
      (anchors.sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)).card := by
    refine Finset.card_le_card_of_injOn (fun K => enc K) ?_ hinj
    intro K hK
    rw [Finset.mem_coe] at hK
    obtain ⟨hanc, hlen⟩ := hmaps K hK
    rw [Finset.mem_coe, Finset.mem_sigma]
    exact ⟨hanc, SimpleGraph.mem_finsetWalkLength_iff.mpr hlen⟩
  have hTcard := card_circuits_based_in_le_pow d anchors ℓ
  have hfinal : (ccb_contourFiber d n ℓ).card ≤ ℓ * (2 * d) ^ ℓ :=
    le_trans hcardfib (le_trans hTcard (Nat.mul_le_mul_right _ hcard))
  change ((ccb_contourFiber d n ℓ).card : ℝ) ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ
  calc ((ccb_contourFiber d n ℓ).card : ℝ) ≤ ((ℓ * (2 * d) ^ ℓ : ℕ) : ℝ) := by
        exact_mod_cast hfinal
    _ = (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ := by push_cast; ring


theorem ccb_contourEncodingExists_of_decode (n ℓ : ℕ)
    (anchors : Finset (Site d)) (hanc : anchors.card ≤ ℓ)
    (enc : Finset (Site d) → Σ v : Site d, (hypercubicLattice d).Walk v v)
    (hmaps : ∀ K ∈ ccb_contourFiber d n ℓ, (enc K).1 ∈ anchors ∧ (enc K).2.length = ℓ)
    (decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)))
    (hdec : ∀ K ∈ ccb_contourFiber d n ℓ,
      decode (enc K) = crossEdges (↑K) (bondFinsetTouch d n)) :
    ccb_ContourEncodingExists d n ℓ := by
  refine ⟨anchors, hanc, enc, hmaps, ?_⟩
  intro K hK K' hK' heq
  rw [Finset.mem_coe, ccb_contourFiber, Finset.mem_filter] at hK hK'
  have hbd : crossEdges (↑K) (bondFinsetTouch d n) = crossEdges (↑K') (bondFinsetTouch d n) := by
    rw [← hdec K (by rw [ccb_contourFiber, Finset.mem_filter]; exact hK),
        ← hdec K' (by rw [ccb_contourFiber, Finset.mem_filter]; exact hK'), heq]
  exact ccb_crossEdges_injOn (ccb_connClusterFamily_props hK.1)
    (ccb_connClusterFamily_props hK'.1) hbd


theorem ccb_peierls_long_range_order_of_encoding (hd : 2 ≤ d)
    (hEnc : ∀ (n ℓ : ℕ), ccb_ContourEncodingExists d n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      Ising.plusMeasure d n β 0 ≠ Ising.minusMeasure d n β 0 :=
  Ising.pcl_peierls_long_range_order_of_count hd
    (fun n => ccb_connectedContourCount_of_encoding (fun ℓ => hEnc n ℓ))

end Lattice
end StatMech
