/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


theorem isClosed_nonneg_smul_of_compact {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (K : Set H) (hK : IsCompact K) (h0 : (0 : H) ∉ K) :
    IsClosed {z : H | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ K, z = t • x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro zn z hzn hlim
  choose t ht x hx hz using hzn
  obtain ⟨x0, hx0K, ψ, hψmono, hψlim⟩ := hK.tendsto_subseq hx
  have hx0pos : 0 < ‖x0‖ := by
    rw [norm_pos_iff]; rintro rfl; exact h0 hx0K
  have hzlim : Tendsto (fun n => zn (ψ n)) atTop (𝓝 z) := hlim.comp hψmono.tendsto_atTop
  have hnormx : Tendsto (fun n => ‖x (ψ n)‖) atTop (𝓝 ‖x0‖) :=
    (continuous_norm.tendsto x0).comp hψlim
  have heqt : ∀ n, t (ψ n) = ‖zn (ψ n)‖ / ‖x (ψ n)‖ := by
    intro n
    rcases eq_or_ne (x (ψ n)) 0 with hx0 | hx0
    · exact absurd (hx0 ▸ hx (ψ n)) h0
    · have hnz : ‖zn (ψ n)‖ = t (ψ n) * ‖x (ψ n)‖ := by
        rw [hz (ψ n), norm_smul, Real.norm_of_nonneg (ht (ψ n))]
      rw [hnz, mul_div_assoc, div_self (by rwa [norm_ne_zero_iff]), mul_one]
  have htlim : Tendsto (fun n => t (ψ n)) atTop (𝓝 (‖z‖ / ‖x0‖)) := by
    simp_rw [heqt]
    exact ((continuous_norm.tendsto z).comp hzlim).div hnormx (ne_of_gt hx0pos)
  refine ⟨‖z‖ / ‖x0‖, div_nonneg (norm_nonneg _) (norm_nonneg _), x0, hx0K, ?_⟩
  have hconv : Tendsto (fun n => zn (ψ n)) atTop (𝓝 ((‖z‖ / ‖x0‖) • x0)) := by
    have := htlim.smul hψlim; simpa [hz] using this
  exact tendsto_nhds_unique hzlim hconv


end Transport
end StatMech
