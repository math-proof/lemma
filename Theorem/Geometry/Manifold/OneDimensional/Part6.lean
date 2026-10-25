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
import Def.Geometry.Manifold.OneDimensional.Part5
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

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

section BoundaryInterior

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Each cap in the union is open. -/
theorem omb_sideCap_open (u : Set M) (hu : IsOpen u) :
    IsOpen (ombSideCap M u) := by
  unfold ombSideCap
  apply hu.union
  apply isOpen_iUnion; intro p
  apply isOpen_iUnion; intro _
  apply isOpen_iUnion; intro ε
  apply isOpen_iUnion; intro hε
  apply isOpen_iUnion; intro _
  exact omb_halfCurve_image_open M p ε ε hε le_rfl

/-- Points of the interior in a side cap lie in the side. -/
theorem omb_mem_of_sideCap_inter (u : Set M)
    (x : M) (hxS : x ∈ (ombInterior M : Set M)) (hx : x ∈ ombSideCap M u) :
    x ∈ u := by
  unfold ombSideCap at hx
  rcases hx with h | h
  · exact h
  · simp only [Set.mem_iUnion] at h
    obtain ⟨p, hp, ε, hε, htail, hcap⟩ := h
    exact omb_cap_inter_subset M p hp ε ε le_rfl u htail ⟨hcap, hxS⟩

/-- The interior is preconnected. -/
theorem omb_isPreconnected_ombInterior [ConnectedSpace M] :
    IsPreconnected (ombInterior M : Set M) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcover hdisj
  have hU'open : IsOpen (ombSideCap M u) := omb_sideCap_open M u hu
  have hV'open : IsOpen (ombSideCap M v) := omb_sideCap_open M v hv
  have hSU : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M u → x ∈ u :=
    fun x hxS hx => omb_mem_of_sideCap_inter M u x hxS hx
  have hSV : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M v → x ∈ v :=
    fun x hxS hx => omb_mem_of_sideCap_inter M v x hxS hx
  have hdisj' : ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxU, hxV⟩, hxS⟩
    have hxu := hSU x hxS hxU
    have hxv := hSV x hxS hxV
    have hmem : x ∈ (ombInterior M : Set M) ∩ (u ∩ v) := ⟨hxS, hxu, hxv⟩
    rw [hdisj] at hmem
    exact Set.notMem_empty x hmem
  have hUV : ombSideCap M u ∩ ombSideCap M v = ∅ := by
    by_contra hne
    have hne' : (ombSideCap M u ∩ ombSideCap M v).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hdense : Dense (ombInterior M : Set M) :=
      dense_iff_closure_eq.mpr (omb_closure_ombInterior M)
    obtain ⟨y, hyUV, hyS⟩ :=
      (dense_iff_inter_open.mp hdense) _ (hU'open.inter hV'open) hne'
    have hmem : y ∈ ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) :=
      ⟨hyUV, hyS⟩
    rw [hdisj'] at hmem
    exact Set.notMem_empty y hmem
  have hcoverM : (Set.univ : Set M) ⊆ ombSideCap M u ∪ ombSideCap M v := by
    intro x _
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x
      with h | h
    · have hxS : x ∈ (ombInterior M : Set M) :=
        SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M x).mpr h)
      rcases hcover hxS with hxu | hxv
      · exact Or.inl (Or.inl hxu)
      · exact Or.inr (Or.inl hxv)
    · obtain ⟨ε, hε, hside⟩ := omb_tail_side M u v hu hv hcover hdisj x h
      rcases hside with htail | htail
      · refine Or.inl (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
      · refine Or.inr (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
  have hUVdisj : (Set.univ : Set M) ∩ (ombSideCap M u ∩ ombSideCap M v) = ∅ := by
    rw [Set.univ_inter]
    exact hUV
  rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ)
    _ _ hU'open hV'open hcoverM hUVdisj with hU | hV
  · exact Or.inl (fun x hxS => hSU x hxS (hU (Set.mem_univ x)))
  · exact Or.inr (fun x hxS => hSV x hxS (hV (Set.mem_univ x)))

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
