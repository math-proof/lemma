/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Def.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part2


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable {tangent : ∀ n, A.M n → Complex}

variable (I : A.StableFullMedialInterpolation tangent)


theorem StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor
    (H : A.MeshUniformCompactHolder I.interpolant)
    (B : Real) (hanchor : ∀ n, ‖I.interpolant n A.root‖ ≤ B) :
    I.HasCompactLocalBounds := by
  intro K hK hKU
  let K' : Set Complex := insert A.root K
  have hK' : IsCompact K' := hK.insert A.root
  have hK'U : K' ⊆ A.U := by
    intro z hz
    rcases hz with rfl | hz
    · exact A.root_mem
    · exact hKU hz
  obtain ⟨C, alpha, _halpha, hholder⟩ := H.holder K' hK' hK'U
  have hdistContinuous : Continuous (fun z : Complex ↦ dist z A.root) :=
    continuous_id.dist continuous_const
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    hdistContinuous.continuousOn
  refine ⟨B + (C : Real) * D ^ (alpha : Real), ?_⟩
  intro n z hz
  have hz' : z ∈ K' := Or.inr hz
  have hroot' : A.root ∈ K' := Or.inl rfl
  calc
    ‖I.interpolant n z‖ ≤ ‖I.interpolant n A.root‖ +
        ‖I.interpolant n z - I.interpolant n A.root‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ = ‖I.interpolant n A.root‖ +
        dist (I.interpolant n z) (I.interpolant n A.root) := by
      rw [dist_eq_norm]
    _ ≤ B + (C : Real) * dist z A.root ^ (alpha : Real) :=
      add_le_add (hanchor n) ((hholder n).dist_le hz' hroot')
    _ ≤ B + (C : Real) * D ^ (alpha : Real) := by
      gcongr
      simpa [Real.norm_of_nonneg dist_nonneg] using hD z hz


theorem StableFullMedialInterpolation.scalingLimit_of_tensorTentCompactHolder
    (H : A.MeshUniformCompactHolder I.interpolant)
    (B : Real) (hanchorBound : ∀ n, ‖I.interpolant n A.root‖ ≤ B)
    (target Phi : Complex → Complex)
    (htarget : DifferentiableOn Complex target A.U)
    (htarget_ne : target A.root ≠ 0)
    (hPhi : DifferentiableOn Complex Phi A.U)
    (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hidentify : StableFullMedialInterpolation.SubsequentialMoreraPrimitive
      A I target Phi) :
    TendstoLocallyUniformlyOn I.interpolant target atTop A.U := by
  exact StableFullMedialInterpolation.scalingLimit_of_compactBounds_and_moreraPrimitive
    A I target Phi htarget htarget_ne hPhi hPhideriv E
      (StableFullMedialInterpolation.hasCompactLocalBounds_of_compactHolder_anchor
        A I H B hanchorBound) hidentify

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
