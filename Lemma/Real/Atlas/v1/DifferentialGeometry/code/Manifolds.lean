import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
open LinearMap (ker range) Set Filter Hypersurface
open scoped Topology
open Set Filter
open scoped InnerProductSpace
open Finset


/--
[ContinuousLinearMap.range_eq_top_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma ContinuousLinearMap.range_eq_top_of_ne_zero
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {f : E →L[ℝ] ℝ}
-- given
  (hf : f ≠ 0) :
-- imply
  (f : E →ₗ[ℝ] ℝ).range = ⊤ := by
-- proof
  rw [Submodule.eq_top_iff']
  intro c
  have ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext (fun v => h v))
  exact ⟨(c / f v) • v, by simp [hv]⟩

/--
[inverse_function_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma inverse_function_theorem
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {φ : E → F}
  {y : E}
  {f' : E ≃L[ℝ] F}
-- given
  (hφ_smooth : ContDiff ℝ ⊤ φ)
  (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y) :
-- imply
  ∃ (Φ : OpenPartialHomeomorph E F), (∀ x ∈ Φ.source, Φ x = φ x) ∧ y ∈ Φ.source ∧ IsOpen Φ.source ∧ IsOpen Φ.target ∧ ContDiffOn ℝ ⊤ Φ Φ.source ∧ ContDiffOn ℝ ⊤ Φ.symm Φ.target := by
-- proof
  let Φ₀ := hf'.toOpenPartialHomeomorph φ
  have hopen_equiv : IsOpen (Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F))) := ContinuousLinearEquiv.isOpen
  have hy_mem : fderiv ℝ φ y ∈ Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F)) := ⟨f', (hf'.hasFDerivAt.fderiv).symm⟩
  have htop_ne : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
  have hcont_fderiv : Continuous (fderiv ℝ φ) := hφ_smooth.continuous_fderiv htop_ne
  let W := fderiv ℝ φ ⁻¹' (Set.range ContinuousLinearEquiv.toContinuousLinearMap)
  have hW_open : IsOpen W := hcont_fderiv.isOpen_preimage _ hopen_equiv
  have hy_W : y ∈ W := hy_mem
  let Φ := Φ₀.restrOpen W hW_open
  have hΦ_source : Φ.source = Φ₀.source ∩ W := Φ₀.restrOpen_source W hW_open
  have hy_source : y ∈ Φ.source := by
    rw [hΦ_source]
    exact ⟨hf'.mem_toOpenPartialHomeomorph_source, hy_W⟩
  have hΦ_eq : (Φ : E → F) = φ := by
    have h1 : (Φ₀ : E → F) = φ := hf'.toOpenPartialHomeomorph_coe
    have h2 : (Φ : E → F) = (Φ₀ : E → F) := Φ₀.coe_restrOpen hW_open
    exact h2.trans h1
  refine ⟨Φ, ?_, hy_source, Φ.open_source, Φ.open_target, ?_, ?_⟩
  · intro x _
    exact congr_fun hΦ_eq x
  · exact hΦ_eq ▸ hφ_smooth.contDiffOn
  · rw [Φ.open_target.contDiffOn_iff]
    intro a ha
    have hsymm_source : Φ.symm a ∈ Φ.source := Φ.map_target ha
    have hsymm_W : Φ.symm a ∈ W := by
      rwa [hΦ_source] at hsymm_source
    obtain ⟨e, he⟩ := hsymm_W
    have hhas_fderiv_Φ : HasFDerivAt (Φ : E → F) (e : E →L[ℝ] F) (Φ.symm a) := by
      have hfderiv_eq : fderiv ℝ φ (Φ.symm a) = (e : E →L[ℝ] F) := he.symm
      have hhas_fderiv : HasFDerivAt φ (e : E →L[ℝ] F) (Φ.symm a) := by
        rw [← hfderiv_eq]
        exact (hφ_smooth.differentiable htop_ne).differentiableAt.hasFDerivAt
      rwa [hΦ_eq]
    have hcd : ContDiffAt ℝ ⊤ (Φ : E → F) (Φ.symm a) := by
      rwa [hΦ_eq]
    exact Φ.contDiffAt_symm ha hhas_fderiv_Φ hcd
section InverseFunctionTheoremLemmas
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/--
[inverse_function_theorem_local_homeomorph](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma inverse_function_theorem_local_homeomorph
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [CompleteSpace E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {φ : E → F}
  {y : E}
  {f' : E ≃L[ℝ] F}
-- given
  (hφ_smooth : ContDiff ℝ ⊤ φ)
  (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y) :
-- imply
  ∃ (Φ : OpenPartialHomeomorph E F), (∀ x ∈ Φ.source, Φ x = φ x) ∧ y ∈ Φ.source ∧ IsOpen Φ.source ∧ IsOpen Φ.target ∧ ContDiffOn ℝ ⊤ Φ Φ.source := by
-- proof
  let Φ := hf'.toOpenPartialHomeomorph φ
  exact ⟨Φ, fun _ _ => rfl,
    hf'.mem_toOpenPartialHomeomorph_source,
    Φ.open_source,
    Φ.open_target,
    hφ_smooth.contDiffOn⟩
end InverseFunctionTheoremLemmas

namespace Hypersurface

/--
[IsLocalDefiningFunction.differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsLocalDefiningFunction.differentiableAt
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hψ : IsLocalDefiningFunction ψ M y) :
-- imply
  DifferentiableAt ℝ ψ y := by
-- proof
  obtain ⟨U, hUo, hyU, hψU, _⟩ := hψ.exists_open_nhd
  exact (hψU.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hyU)

end Hypersurface

namespace Hypersurface

/--
[mem_tangentSpace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma mem_tangentSpace_iff
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {y v : E} :
-- imply
  v ∈ tangentSpace ψ y ↔ fderiv ℝ ψ y v = 0 := by
-- proof
  simp [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

end Hypersurface

namespace Hypersurface

/--
[IsLocalDefiningFunction.eq_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsLocalDefiningFunction.eq_zero_of_mem
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hψ : IsLocalDefiningFunction ψ M y)
  (hy : y ∈ M) :
-- imply
  ψ y = 0 := by
-- proof
  obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
  exact (hU y hyU).mp hy

end Hypersurface

namespace Hypersurface

/--
[IsLocalDefiningFunction.isRegularPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsLocalDefiningFunction.isRegularPoint
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hψ : IsLocalDefiningFunction ψ M y) :
-- imply
  IsRegularPoint ψ y :=
-- proof
  ⟨hψ.differentiableAt, hψ.fderiv_ne_zero⟩

end Hypersurface

namespace Hypersurface

/--
[IsSmoothLocalDefiningFunction.toIsLocalDefiningFunction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsSmoothLocalDefiningFunction.toIsLocalDefiningFunction
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hy : y ∈ M)
  (h : IsSmoothLocalDefiningFunction ψ M y) :
-- imply
  IsLocalDefiningFunction ψ M y := by
-- proof
  obtain ⟨V, hVo, hyV, hψV, hzero, hderiv⟩ := h.exists_open_nhd
  exact {
    exists_open_nhd := ⟨V, hVo, hyV, hψV.of_le le_top, hzero⟩
    fderiv_ne_zero := hderiv y hyV hy
  }

end Hypersurface

namespace Hypersurface

/--
[IsSmoothLocalDefiningFunction.eq_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsSmoothLocalDefiningFunction.eq_zero_of_mem
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hψ : IsSmoothLocalDefiningFunction ψ M y)
  (hy : y ∈ M) :
-- imply
  ψ y = 0 := by
-- proof
  obtain ⟨V, _, hyV, _, hzero, _⟩ := hψ.exists_open_nhd
  exact (hzero y hyV).mp hy

end Hypersurface

namespace Hypersurface

/--
[IsSmoothLocalDefiningFunction.isRegularPoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma IsSmoothLocalDefiningFunction.isRegularPoint
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
-- given
  (hψ : IsSmoothLocalDefiningFunction ψ M y)
  (hy : y ∈ M) :
-- imply
  IsRegularPoint ψ y := by
-- proof
  obtain ⟨V, hVo, hyV, hψV, _, hderiv⟩ := hψ.exists_open_nhd
  exact ⟨(hψV.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds hyV),
    hderiv y hyV hy⟩

end Hypersurface

namespace Hypersurface

/--
[tangent_of_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma tangent_of_curve
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y v : E}
  {c : ℝ → E}
-- given
  (hψ : IsLocalDefiningFunction ψ M y)
  (hc : IsTangentCurve c M y v) :
-- imply
  v ∈ tangentSpace ψ y := by
-- proof
  rw [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  obtain ⟨U, hUo, hyU, hψU, hzero⟩ := hψ.exists_open_nhd
  have hψ_diff : DifferentiableAt ℝ ψ y :=
    (hψU.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt (hUo.mem_nhds hyU)
  have hψ_hasFDerivAt : HasFDerivAt ψ (fderiv ℝ ψ y) y := hψ_diff.hasFDerivAt
  have hchain : HasDerivAt (ψ ∘ c) ((fderiv ℝ ψ y) v) 0 := by
    have key : HasFDerivAt ψ (fderiv ℝ ψ y) (c 0) := by rw [hc.at_zero]; exact hψ_hasFDerivAt
    exact key.comp_hasDerivAt 0 hc.hasDerivAt
  have hconst : HasDerivAt (ψ ∘ c) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    have h1 : ∀ᶠ t in 𝓝 0, c t ∈ U := by
      have hcont : ContinuousAt c 0 := hc.hasDerivAt.continuousAt
      exact hcont.preimage_mem_nhds (by rw [hc.at_zero]; exact hUo.mem_nhds hyU)
    filter_upwards [h1, hc.image_in_M] with t ht1 ht2
    simp [Function.comp, (hzero (c t) ht1).mp ht2]
  exact hchain.unique hconst

end Hypersurface

namespace Hypersurface

/--
[curve_of_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean)
-/
@[path]
lemma curve_of_tangent
  {n : ℕ}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {ψ : E → ℝ}
  {M : Set E}
  {y : E}
  {v : E}
-- given
  (hψ : IsLocalDefiningFunction ψ M y)
  (hy : y ∈ M)
  (hv : v ∈ tangentSpace ψ y)
  (hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y) :
-- imply
  ∃ c : ℝ → E, IsTangentCurve c M y v := by
-- proof
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hrange : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).range = ⊤ :=
    ContinuousLinearMap.range_eq_top_of_ne_zero _ hψ.fderiv_ne_zero
  let g := hstrict.implicitFunction ψ (fderiv ℝ ψ y) hrange
  have hψ_zero : ψ y = 0 := by
    obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
    exact (hU y hyU).mp hy
  have hg_zero : g 0 0 = y := by
    have := hstrict.implicitFunction_apply_image hrange
    rwa [hψ_zero] at this
  have hg_map : ∀ᶠ p : ℝ × (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker in
    𝓝 (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)),
    ψ (g p.1 p.2) = p.1 := by
    have := hstrict.map_implicitFunction_eq hrange
    rwa [hψ_zero] at this
  have hg_deriv : HasStrictFDerivAt (g 0)
    (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL 0 := by
    have := hstrict.to_implicitFunction hrange
    rwa [hψ_zero] at this
  have hv_mem : v ∈ (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := by
    rwa [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  let w : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := ⟨v, hv_mem⟩
  have hderiv_c : HasDerivAt (fun t : ℝ => g 0 (t • w)) v 0 := by
    have hderiv_smul : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have key : (fun t : ℝ => t • w) 0 = 0 := by simp
    have hg' : HasFDerivAt (g 0) (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL
      ((fun t : ℝ => t • w) 0) := by
      rw [key]; exact hg_deriv.hasFDerivAt
    have hcomp := hg'.comp_hasDerivAt (x := (0 : ℝ)) hderiv_smul
    simp at hcomp
    exact hcomp
  let c : ℝ → E := fun t => g 0 (t • w)
  refine ⟨c, ?_, ?_, ?_⟩
  · show g 0 ((0 : ℝ) • w) = y
    simp [hg_zero]
  · exact hderiv_c
  · show ∀ᶠ t in 𝓝 0, g 0 (t • w) ∈ M
    obtain ⟨U, hUo, hyU, _, hzero⟩ := hψ.exists_open_nhd
    have hψ_eq_zero : ∀ᶠ t in 𝓝 (0 : ℝ), ψ (g 0 (t • w)) = 0 := by
      have hcont_tw : ContinuousAt (fun t : ℝ => ((0 : ℝ), t • w)) 0 := by fun_prop
      have h0 : (fun t : ℝ => ((0 : ℝ), t • w)) 0 =
        (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)) := by simp
      have hmem := hcont_tw.eventually (h0 ▸ hg_map)
      simpa [Function.comp] using hmem
    have hcont_c : ContinuousAt c 0 := hderiv_c.continuousAt
    have hc_in_U : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U := by
      apply hcont_c.preimage_mem_nhds
      change U ∈ 𝓝 (c 0)
      simp only [c, zero_smul, hg_zero]
      exact hUo.mem_nhds hyU
    filter_upwards [hψ_eq_zero, hc_in_U] with t ht1 ht2
    exact (hzero (g 0 (t • w)) ht2).mpr ht1

end Hypersurface


-- created on 2026-10-23
