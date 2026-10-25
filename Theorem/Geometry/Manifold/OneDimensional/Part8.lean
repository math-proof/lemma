/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Geometry.Manifold.Instances.Sphere
import Lemma.Set.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.Geometry.Manifold.OneDimensional.Part6
open scoped Manifold ContDiff Topology Bundle


section LocalDiffeomorphConstructors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

end LocalDiffeomorphConstructors
section IntervalParametrisation
end IntervalParametrisation
section InverseFunction1D
end InverseFunction1D
noncomputable section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

open MathlibExt.Geometry.Manifold.OneDimensionalClassification

/-- On the tail, `Ψ (θ t)` recovers the half-curve. -/
theorem omb_theta_apply (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    ((Ψ (ombTheta M Ψ x₀ p t) : ↥(ombInterior M)) : M)
      = ombHalfCurve M p t := by
  have hmemO : ombHalfCurve M p t ∈ ombInterior M :=
    omb_halfCurve_mem_interior M p ε t hε ht
  have e : ombTheta M Ψ x₀ p t
      = Ψ.symm (ombRetract M x₀ (ombHalfCurve M p t)) := rfl
  rw [e, Ψ.apply_symm_apply, ombRetract_of_mem M x₀ _ hmemO]

/-- The end map is a local diffeomorphism on the tail. -/
theorem omb_isLocalDiffeomorphAt_theta (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (ombTheta M Ψ x₀ p) t := by
  have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) t :=
    omb_isLocalDiffeomorphAt_halfCurve M p ε t hε ht
  have hmem : ombHalfCurve M p t ∈ (ombInterior M : Set M) :=
    SetLike.mem_coe.mp (omb_halfCurve_mem_interior M p ε t hε ht)
  have h2 : IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀)
      (ombHalfCurve M p t) :=
    omb_isLocalDiffeomorphAt_retract M x₀ _ hmem
  have h3 : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (⇑Ψ.symm)
      (ombRetract M x₀ (ombHalfCurve M p t)) :=
    Ψ.symm.isLocalDiffeomorph _
  have h12 := IsLocalDiffeomorphAt.comp (K := (𝓡 1)) (P := ↥(ombInterior M)) h1 h2
  have h := IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) h12 h3
  have e : (⇑Ψ.symm ∘ ombRetract M x₀ ∘ ombHalfCurve M p)
      = ombTheta M Ψ x₀ p := rfl
  rw [e] at h
  exact h

/-- The end map is smooth on the tail interval. -/
theorem omb_theta_contDiffOn (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    ContDiffOn ℝ ∞ (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
  intro t ht
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  exact h.contMDiffAt.contDiffAt.contDiffWithinAt

/-- The derivative of the end map never vanishes on the tail. -/
theorem omb_theta_deriv_ne (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    deriv (ombTheta M Ψ x₀ p) t ≠ 0 := by
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  have hinv := h.isInvertible_mfderiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  have heq : (fderiv ℝ (ombTheta M Ψ x₀ p) t)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ombTheta M Ψ x₀ p) t) :=
    mfderiv_eq_fderiv.symm
  have hinv2 : (fderiv ℝ (ombTheta M Ψ x₀ p) t).IsInvertible := heq ▸ hinv
  obtain ⟨A, hA⟩ := hinv2
  have h1 : (fderiv ℝ (ombTheta M Ψ x₀ p) t) 1 ≠ 0 := by
    rw [← hA]
    have hA1 : A (1 : ℝ) ≠ A 0 := by
      intro hcon
      exact one_ne_zero (A.injective hcon)
    rwa [map_zero] at hA1
  rwa [fderiv_apply_one_eq_deriv] at h1

/-- The derivative of the end map has constant sign on the tail. -/
theorem omb_theta_deriv_sign (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    (∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) ∨
      (∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) := by
  have hne : ∀ t ∈ Set.Ioo (0 : ℝ) ε, deriv (ombTheta M Ψ x₀ p) t ≠ 0 :=
    fun t ht => omb_theta_deriv_ne M Ψ x₀ p ε hε t ht
  have hcont : ContinuousOn (deriv (ombTheta M Ψ x₀ p)) (Set.Ioo 0 ε) :=
    (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn_deriv_of_isOpen isOpen_Ioo
      (by simp : (1 : ℕ∞ω) ≤ ∞)
  by_cases h : ∃ t ∈ Set.Ioo (0 : ℝ) ε, 0 < deriv (ombTheta M Ψ x₀ p) t
  · left
    obtain ⟨a, ha, hapos⟩ := h
    intro t ht
    rcases lt_trichotomy (deriv (ombTheta M Ψ x₀ p) t) 0 with hneg | hzero | hpos
    · exfalso
      obtain ⟨c, hc, hczero⟩ := isPreconnected_Ioo.intermediate_value₂ ht ha
        hcont continuousOn_const (le_of_lt hneg) (le_of_lt hapos)
      exact hne c hc hczero
    · exact absurd hzero (hne t ht)
    · exact hpos
  · right
    push Not at h
    intro t ht
    rcases lt_or_gt_of_ne (hne t ht) with hneg | hpos
    · exact hneg
    · have hle := h t ht
      linarith

/-- A two-sided bound on a tail interval is impossible. -/
theorem omb_theta_bounded_false (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (δ : ℝ) (hδpos : 0 < δ) (hδε : δ ≤ ε) (lo hi : ℝ)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) δ, ombTheta M Ψ x₀ p t ∈ Set.Icc lo hi) :
    False := by
  set K : Set M := (fun u : ℝ => ((Ψ u : ↥(ombInterior M)) : M)) ''
    Set.Icc lo hi with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    apply IsCompact.image isCompact_Icc
    exact continuous_subtype_val.comp Ψ.continuous
  have hKclosed : IsClosed K := hKc.isClosed
  have hpclosure : p ∈ closure ((ombHalfCurve M p) '' Set.Ioo 0 δ) := by
    apply mem_closure_of_tendsto (omb_halfCurve_tendsto M p hp ε hε)
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht
    exact ⟨t, ht, rfl⟩
  have hsub : (ombHalfCurve M p) '' Set.Ioo 0 δ ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    have hθt := hb t ht
    rw [hKdef]
    exact ⟨ombTheta M Ψ x₀ p t, hθt,
      omb_theta_apply M Ψ x₀ p ε hε t htε⟩
  have hpK : p ∈ K := closure_minimal hsub hKclosed hpclosure
  obtain ⟨u, _, hpu⟩ := hpK
  have hpS : p ∈ (ombInterior M : Set M) := by
    rw [← hpu]
    exact (Ψ u).2
  have hnot : p ∉ ombInterior M := omb_boundary_not_mem_interior M p hp
  exact hnot (SetLike.mem_coe.mpr hpS)

/-- Increasing end map tends to `atBot`. -/
theorem omb_theta_tendsto_atBot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hpos : ∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot := by
  have hmono : StrictMonoOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hpos
  rw [Filter.tendsto_atBot]
  intro B
  obtain ⟨t₀, ht₀, hlt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, ombTheta M Ψ x₀ p t < B := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε B
      (ombTheta M Ψ x₀ p (ε / 2))
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨hcon t htε, ?_⟩
    exact le_of_lt (hmono htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans (hmono htε ht₀ ht.2) hlt)

/-- Decreasing end map tends to `atTop`. -/
theorem omb_theta_tendsto_atTop (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hneg : ∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  have hanti : StrictAntiOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hneg
  rw [Filter.tendsto_atTop]
  intro B
  obtain ⟨t₀, ht₀, hgt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, B < ombTheta M Ψ x₀ p t := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε
      (ombTheta M Ψ x₀ p (ε / 2)) B
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨?_, hcon t htε⟩
    exact le_of_lt (hanti htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans hgt (hanti htε ht₀ ht.2))

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
end
