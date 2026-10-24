import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.TensorO


/--
[IsCategoryO_of_lieEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TensorO.lean)
-/
@[path]
private lemma IsCategoryO_of_lieEquiv
  [CommRing R]
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  [AddCommGroup A]
  [Module R A]
  [LieRingModule 𝔤 A]
  [LieModule R 𝔤 A]
  [AddCommGroup B]
  [Module R B]
  [LieRingModule 𝔤 B]
  [LieModule R 𝔤 B]
  {f : A ≃ₗ⁅R, 𝔤⁆ B}
-- given
  (hB : IsCategoryO Δ rd B) :
-- imply
  IsCategoryO Δ rd A where finitely_generated := by
-- proof
  obtain ⟨S, hS⟩ := hB.finitely_generated
  set T := S.map ⟨f.symm, f.symm.injective⟩ with hT_def
  refine ⟨T, ?_⟩
  set N := LieSubmodule.lieSpan R 𝔤 (↑T : Set A) with hN_def
  set fN := LieSubmodule.map f.toLieModuleHom N with hfN_def
  have hS_sub_fN : (↑S : Set B) ⊆ (fN : Set B) := by
    intro s hs
    show s ∈ fN
    rw [hfN_def, LieSubmodule.mem_map]
    exact ⟨f.symm s, LieSubmodule.subset_lieSpan (by
      rw [hT_def, Finset.coe_map]; exact ⟨s, hs, rfl⟩),
      f.apply_symm_apply s⟩
  have hfN_eq_top : fN = ⊤ := by
    rw [eq_top_iff, ← hS]
    exact LieSubmodule.lieSpan_le.mpr hS_sub_fN
  rw [eq_top_iff]
  intro a _
  have hfa_in : f a ∈ fN := hfN_eq_top ▸ LieSubmodule.mem_top _
  rw [hfN_def, LieSubmodule.mem_map] at hfa_in
  obtain ⟨a', ha', hfa'⟩ := hfa_in
  have heq : a' = a := f.injective hfa'
  rwa [← heq]
  weight_decomp := by
    intro a
    obtain ⟨S, v, hv⟩ := hB.weight_decomp (f a)
    refine ⟨S, fun μ => ⟨f.symm (v μ : B), fun h => ?_⟩, ?_⟩
    · have hvm := (v μ).prop h
      apply f.injective
      rw [show f ⁅(↑h : 𝔤), f.symm ↑(v μ)⁆ =
        ⁅(↑h : 𝔤), f (f.symm ↑(v μ))⁆ from by
          show (f : A →ₗ⁅R,𝔤⁆ B) ⁅(↑h : 𝔤), f.symm ↑(v μ)⁆ =
            ⁅(↑h : 𝔤), (f : A →ₗ⁅R,𝔤⁆ B) (f.symm ↑(v μ))⁆
          rw [LieModuleHom.map_lie]]
      rw [f.apply_symm_apply, hvm, map_smul, f.apply_symm_apply]
    · apply f.injective
      rw [map_sum]
      simp only [f.apply_symm_apply]
      exact hv
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hB.weight_bound
    refine ⟨bds, fun μ hμ => ?_⟩
    have hμB : μ ∈ weights Δ B := by
      rw [weights, Set.mem_setOf_eq] at hμ ⊢
      intro hbot
      apply hμ
      rw [eq_bot_iff]
      intro a ha
      have hfa : f a ∈ WeightSpace Δ B μ := by
        intro hh
        show ⁅(↑hh : 𝔤), (f : A →ₗ⁅R,𝔤⁆ B) a⁆ = μ hh • (f : A →ₗ⁅R,𝔤⁆ B) a
        rw [← LieModuleHom.map_lie, ha hh, map_smul]
      rw [hbot] at hfa
      simp [Submodule.mem_bot] at hfa
      exact hfa
    exact hbds μ hμB

/--
[tensor_verma_projective_of_dominant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TensorO.lean)
-/
@[path]
private lemma tensor_verma_projective_of_dominant
  {R : Type v}
  [Field R]
  {𝔤 : Type v}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {Mlam : Type v}
  [AddCommGroup Mlam]
  [Module R Mlam]
  [LieRingModule 𝔤 Mlam]
  [LieModule R 𝔤 Mlam]
  {lam : Δ.𝔥 →ₗ[R] R}
  {V : Type v}
  [AddCommGroup V]
  [Module R V]
  [LieRingModule 𝔤 V]
  [LieModule R 𝔤 V]
  [Module.Finite R V]
  [Module.Free R V]
  {VP : Type v}
  [AddCommGroup VP]
  [Module R VP]
  [LieRingModule 𝔤 VP]
  [LieModule R 𝔤 VP]
  {tensor_iso : VP ≃ₗ⁅R, 𝔤⁆ TensorProduct R V Mlam}
-- given
  (hdom : IsDominantWeightLE rd wg lam)
  (hMlam : IsVermaModule Δ Mlam (lam - wg.ρ))
  (hMlamO : IsCategoryO Δ rd Mlam)
  (hVPO : IsCategoryO Δ rd VP) :
-- imply
  IsProjectiveInO rd VP hVPO := by
-- proof
  have hMlam_proj : IsProjectiveInO rd Mlam hMlamO :=
    verma_projective_of_dominant lam hdom hMlam hMlamO
  exact tensor_projective_in_O hMlamO hMlam_proj hVPO tensor_iso


-- created on 2026-10-23
-- updated on 2026-10-24
