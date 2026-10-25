/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem symmDiff_eq_symmDiff_iff_of_separated (S X Y A B : Finset V)
    (hXS : X ⊆ S) (hYS : Y ⊆ Sᶜ) (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ) :
    X ∆ Y = A ∆ B ↔ X = A ∧ Y = B := by
  constructor
  · intro h
    constructor <;> ext v
    · have hv := Finset.ext_iff.mp h v
      by_cases hs : v ∈ S
      · have hny : v ∉ Y := fun hy => (Finset.mem_compl.mp (hYS hy)) hs
        have hnb : v ∉ B := fun hb => (Finset.mem_compl.mp (hBS hb)) hs
        simp only [Finset.mem_symmDiff] at hv
        simpa [hny, hnb] using hv
      · have hnx : v ∉ X := fun hx => hs (hXS hx)
        have hna : v ∉ A := fun ha => hs (hAS ha)
        simp [hnx, hna]
    · have hv := Finset.ext_iff.mp h v
      by_cases hs : v ∈ S
      · have hny : v ∉ Y := fun hy => (Finset.mem_compl.mp (hYS hy)) hs
        have hnb : v ∉ B := fun hb => (Finset.mem_compl.mp (hBS hb)) hs
        simp [hny, hnb]
      · have hnx : v ∉ X := fun hx => hs (hXS hx)
        have hna : v ∉ A := fun ha => hs (hAS ha)
        simp only [Finset.mem_symmDiff] at hv
        simpa [hnx, hna] using hv
  · rintro ⟨rfl, rfl⟩
    rfl


theorem sources_reEdge_eq_symmDiff_iff (S A B : Finset V)
    (hAS : A ⊆ S) (hBS : B ⊆ Sᶜ)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ)
    (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)
    (hcross : ∀ i : ↥G.edgeFinset, 1 ≤ bFull G S b i → edgeInside Sᶜ (i : Sym2 V)) :
    sources G (ofEdgeFun G (reEdge G S (a, b))) = A ∆ B ↔
      sources G (ofEdgeFun G (aFull G S a)) = A ∧
        sources G (ofEdgeFun G (bFull G S b)) = B := by
  rw [sources_reEdge_split]
  exact symmDiff_eq_symmDiff_iff_of_separated S _ _ A B
    (sources_aFull_subset G S a) (sources_bFull_subset_compl G S b hcross) hAS hBS


end Sharpness
end StatMech
