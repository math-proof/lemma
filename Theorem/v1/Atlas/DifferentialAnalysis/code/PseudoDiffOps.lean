/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionTheorem
import Def.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact
import Def.v1.Atlas.DifferentialAnalysis.code.PseudoDiffOps


noncomputable section

open scoped SchwartzMap Pointwise

open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- If `μ` has compact support in the Schwartz-pairing sense, then its distributional
support `Distribution.dsupport μ` is compact. -/
theorem hasCompactDsupport_of_hasCompactSupport
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    HasCompactDsupport μ := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hμ

  have hclosed := Distribution.isClosed_dsupport (f := μ)

  have hK_closed : IsClosed K := hK_compact.isClosed
  have hvanish : Distribution.IsVanishingOn μ Kᶜ := by
    intro φ hφ
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have hy_tsupp : y ∈ tsupport (⇑φ) := subset_tsupport _ hy_supp
    exact absurd hy_K (Set.mem_compl_iff K y |>.mp (hφ hy_tsupp))
  have hsubset : Distribution.dsupport μ ⊆ K := by
    have hd := hvanish.disjoint_dsupport hK_closed.isOpen_compl
    rwa [Set.disjoint_compl_left_iff_subset] at hd
  exact hK_compact.of_isClosed_subset hclosed hsubset

end DifferentialOperators
end
