/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Lemma.Complex.IsKFinite0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part3


noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]

variable [CompactlySupportedMeasureAlgebra G M]

/-! ### API exports for Lemma.Complex.inner.of.IsUnitary (olean stubs) -/

/-- Schur dichotomy for continuous intertwiner between irreps: zero or bijective. -/
theorem schur_zero_or_iso_continuous
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [TopologicalSpace V₂]
    (π₁ : ContinuousRep G V₁) (π₂ : ContinuousRep G V₂)
    (hirr₁ : π₁.IsIrreducible) (hirr₂ : π₂.IsIrreducible)
    (T : RepHom π₁ π₂) :
    (∀ v, T.toContinuousLinearMap v = 0) ∨ Function.Bijective T.toContinuousLinearMap := by
  sorry

theorem orthogonalProjection_intertwines_subrep_val
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : ContinuousRep G E) (hU : π.IsUnitary) (K : Subgroup G)
    (W₁ W₂ : Submodule ℂ E)
    [W₂.HasOrthogonalProjection]
    (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
    (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂)
    (v : ↥W₁) :
    (orthogonalProjection_intertwines_subrep π hU K W₁ W₂ hW₁ hW₂).toContinuousLinearMap v =
      W₂.orthogonalProjection (v : E) := by
  simp only [orthogonalProjection_intertwines_subrep, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply]

theorem repEquiv_of_bijective_repHom
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [TopologicalSpace V₁] [CompleteSpace V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [TopologicalSpace V₂] [CompleteSpace V₂]
    (π₁ : ContinuousRep G V₁) (π₂ : ContinuousRep G V₂)
    (T : RepHom π₁ π₂) (hbij : Function.Bijective T.toContinuousLinearMap) :
    Nonempty (RepEquiv π₁ π₂) := by
  sorry

theorem repEquiv_trans
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    {V₃ : Type*} [AddCommGroup V₃] [Module ℂ V₃] [TopologicalSpace V₃]
    {π₁ : ContinuousRep G V₁} {π₂ : ContinuousRep G V₂} {π₃ : ContinuousRep G V₃}
    (e₁₂ : Nonempty (RepEquiv π₁ π₂)) (e₂₃ : Nonempty (RepEquiv π₂ π₃)) :
    Nonempty (RepEquiv π₁ π₃) := by
  sorry

theorem repEquiv_symm
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    {π₁ : ContinuousRep G V₁} {π₂ : ContinuousRep G V₂}
    (e : Nonempty (RepEquiv π₁ π₂)) :
    Nonempty (RepEquiv π₂ π₁) := by
  sorry

theorem mem_orthogonal_sSup
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {T : Set (Submodule ℂ F)} {v : F}
    (h : ∀ W ∈ T, v ∈ Wᗮ) :
    v ∈ (sSup T)ᗮ := by
  sorry

theorem sSup_orthogonal_sSup
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {S T : Set (Submodule ℂ F)}
    (h : ∀ U ∈ S, ∀ W ∈ T, U.IsOrtho W) :
    (sSup S).IsOrtho (sSup T) := by
  sorry

/-- Wrapper matching Lemma `μ.sum` call sites; equal to `μ.coeff.sum`. -/
theorem total_variation_eval_cont
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [inst : CompactlySupportedMeasureAlgebra G M]
    (f : G → ℝ) (hf : Continuous f) (hf_nn : ∀ g, 0 ≤ f g) :
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.coeff.sum (fun g c => ‖c‖ * f g)) :=
  inst.total_variation_cont f hf hf_nn

theorem blt_alg_hom_extend
    {α β γ : Type*} [Semiring α] [Semiring β] [Semiring γ]
    [Algebra ℂ α] [Algebra ℂ β] [Algebra ℂ γ]
    [TopologicalSpace β] [ContinuousAdd β] [ContinuousMul β]
    [TopologicalSpace γ] [T2Space γ] [ContinuousAdd γ] [ContinuousMul γ]
    {ι : α →ₐ[ℂ] β} {f : α →ₐ[ℂ] γ} {g_fun : β → γ}
    (h_dense : Dense (Set.range ι))
    (hg_cont : Continuous g_fun)
    (hg_ext : ∀ x : α, g_fun (ι x) = f x) :
    ∃ (g : β →ₐ[ℂ] γ), Continuous g ∧ ∀ x : α, g (ι x) = f x := by
  sorry

theorem CompactlySupportedMeasureAlgebra.discrete_dense
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [inst : CompactlySupportedMeasureAlgebra G M] :
    Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)) := by
  sorry

theorem CompactlySupportedMeasureAlgebra.alg_hom_extend
    {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]
    [ContinuousAdd M] [ContinuousMul M]
    [inst : CompactlySupportedMeasureAlgebra G M]
    {A : Type*} [Ring A] [Algebra ℂ A]
    [TopologicalSpace A] [ContinuousAdd A] [ContinuousMul A] [T2Space A]
    {f : MonoidAlgebra ℂ G →ₐ[ℂ] A}
    (h_dense : Dense (Set.range (MonoidAlgebra.lift ℂ M G inst.dirac)))
    (h_cont : @Continuous (MonoidAlgebra ℂ G) A
      (TopologicalSpace.induced (MonoidAlgebra.lift ℂ M G inst.dirac) ‹TopologicalSpace M›)
      _ f) :
    ∃ (g : M →ₐ[ℂ] A), Continuous g ∧
      ∀ μ : MonoidAlgebra ℂ G, g ((MonoidAlgebra.lift ℂ M G inst.dirac) μ) = f μ := by
  sorry

end Unitary


omit [IsTopologicalGroup G] in
/-- Peter-Weyl: K-finite vectors are dense when K is compact. -/
theorem kFiniteSubspace_dense
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : ContinuousRep G V) (K : Subgroup G) [CompactSpace K] :
    Dense (kFiniteSubspace π K : Set V) := by
  sorry

end ContinuousRep
end
