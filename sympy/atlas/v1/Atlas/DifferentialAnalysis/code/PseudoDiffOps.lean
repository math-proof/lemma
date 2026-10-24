/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConvolutionTheorem
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact

noncomputable section

open scoped SchwartzMap Pointwise
open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` on Euclidean space has compact support if there is a
compact `K` such that `u` annihilates every Schwartz function whose support is disjoint
from `K`. -/
def HasCompactSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ K = ∅) → u φ = 0

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

/-- The reflection `φ ↦ φ ∘ (-id)` as a continuous linear endomorphism of the Schwartz
space `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def schwNegReflCLM :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- Cross-correlation with a compactly supported distribution `μ`, viewed as a continuous
linear endomorphism of `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def crossCorrSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  let hμ' := hasCompactDsupport_of_hasCompactSupport μ hμ
  { toLinearMap :=
      { toFun := compactDsupportConvolutionSchwartzMap μ hμ'
        map_add' := compactDsupportConvolution_map_add μ hμ'
        map_smul' := compactDsupportConvolution_map_smul μ hμ' }
    cont := continuous_compactDsupportConvolution μ hμ' }

/-- Convolution with a compactly supported distribution `μ` on Schwartz functions, given
as the reflection composed with cross-correlation. -/
def convolutionSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  schwNegReflCLM.comp (crossCorrSchwartzCLM μ hμ)

/-- The convolution `μ * f` of two tempered distributions, defined when the left factor
`μ` has compact support, by precomposing `f` with convolution by `μ` on Schwartz test
functions. -/
def distribConvolution
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (PointwiseConvergenceCLM.precomp ℂ (convolutionSchwartzCLM μ hμ)) f

/-- A decomposition of a tempered distribution `u = singular + smooth` into a singular
part with compact support contained in `supportSet` and a globally smooth, compactly
supported part. Used in the proof of `singularSupport_convolution_subset`. -/
structure SmoothDecomp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  singular : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  smooth : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  supportSet : Set (EuclideanSpace ℝ (Fin n))
  supportSet_compact : IsCompact supportSet
  singular_supported :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ supportSet = ∅) → singular φ = 0
  singular_compactSupport : HasCompactSupport singular
  smooth_isSmooth : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear smooth x₀
  smooth_compactSupport : HasCompactSupport smooth
  sum_eq : u = singular + smooth
