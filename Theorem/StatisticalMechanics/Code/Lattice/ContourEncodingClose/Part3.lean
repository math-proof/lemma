/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
open Set Finset SimpleGraph
open StatMech.Ising


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem ccb_contourEncodingExists_of_anchoredBoundaryWalk (n ℓ : ℕ)
    (h : ccb_AnchoredBoundaryWalkExists n ℓ) :
    ccb_ContourEncodingExists 2 n ℓ := by
  obtain ⟨D, hD⟩ := h
  choose! v hv w hwlen hwdec using hD
  refine ccb_contourEncodingExists_of_decode (d := 2) n ℓ (ccb_anchorRow ℓ)
    (ccb_anchorRow_card ℓ) (fun K => ⟨v K, w K⟩) ?_ D ?_
  · intro K hK; exact ⟨hv K hK, hwlen K hK⟩
  · intro K hK; exact hwdec K hK


theorem ccb_anchoredBoundaryWalkExists_of_emptyFiber (n ℓ : ℕ)
    (hempty : ccb_contourFiber 2 n ℓ = ∅) :
    ccb_AnchoredBoundaryWalkExists n ℓ := by
  refine ⟨fun _ => ∅, ?_⟩
  intro K hK
  rw [hempty] at hK
  exact absurd hK (Finset.notMem_empty K)


theorem ccb_peierls_of_anchoredBoundaryWalk
    (h : ∀ (n ℓ : ℕ), ccb_AnchoredBoundaryWalkExists n ℓ) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      Ising.plusMeasure 2 n β 0 ≠ Ising.minusMeasure 2 n β 0 :=
  ccb_peierls_long_range_order_of_encoding (d := 2) le_rfl
    (fun n ℓ => ccb_contourEncodingExists_of_anchoredBoundaryWalk n ℓ (h n ℓ))


end Lattice
end StatMech
