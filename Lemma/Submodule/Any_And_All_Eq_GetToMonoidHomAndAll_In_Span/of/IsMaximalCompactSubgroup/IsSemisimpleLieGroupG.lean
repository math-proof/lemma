import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.AnalyticityRegularity
open ContinuousRep
open scoped Manifold


namespace ContinuousRep

/--
[casimir_exists_nonzero_kEquivariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma casimir_exists_nonzero_kEquivariant
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [Nontrivial F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
-- given
  (_hG_ss : IsSemisimpleLieGroup I G)
  (_hK_max : IsMaximalCompactSubgroup K) :
-- imply
  ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧ (∀ (k : K) (w : F), b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧ (∀ (v : F), v ∈ π.kFiniteSubspace K → b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by
-- proof
  refine ⟨LinearMap.id, ?_, fun k w => by simp, fun v _ => ?_⟩
  · exact fun h => by
    obtain ⟨x, y, hne⟩ := exists_pair_ne F
    exact hne (by
      have := LinearMap.ext_iff.mp h
      simp at this
      rw [this x, this y])
  · simp only [LinearMap.id_apply]
    exact Submodule.subset_span ⟨⟨1, K.one_mem⟩, by simp [map_one]⟩

end ContinuousRep

namespace ContinuousRep

/--
[kEquivariant_preserves_kOrbitSpan](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma kEquivariant_preserves_kOrbitSpan
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
  {b : F →ₗ[ℂ] F}
  {v : F}
-- given
  (hb_comm : ∀ (k : K) (w : F), b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w))
  (hbv : b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) :
-- imply
  ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)), b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
-- proof
  intro w hw
  set W := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) with hW_def
  have hW_inv : ∀ (k₁ : K) (w' : F), w' ∈ W → (π.toMonoidHom ↑k₁) w' ∈ W := by
    intro k₁ w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k₂, rfl⟩ := hx
      have : (π.toMonoidHom ↑k₁) ((π.toMonoidHom ↑k₂) v) =
        (π.toMonoidHom ↑(k₁ * k₂)) v := by
        simp [map_mul]
      rw [this]
      exact Submodule.subset_span ⟨k₁ * k₂, rfl⟩
    | zero => simp [map_zero]
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | smul c x _ hx =>
      rw [ContinuousLinearMap.map_smul]
      exact W.smul_mem c hx
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k₀, rfl⟩ := hx
    rw [hb_comm k₀ v]
    exact hW_inv k₀ (b v) hbv
  | zero => simp [map_zero, W.zero_mem]
  | add x y _ _ hx hy =>
    rw [map_add]
    exact W.add_mem hx hy
  | smul c x _ hx =>
    rw [LinearMap.map_smul]
    exact W.smul_mem c hx

end ContinuousRep

namespace ContinuousRep

/--
[casimir_exists_nonzero_kInvariant_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma casimir_exists_nonzero_kInvariant_aux
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [Nontrivial F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
-- given
  (hG_ss : IsSemisimpleLieGroup I G)
  (hK_max : IsMaximalCompactSubgroup K) :
-- imply
  ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧ (∀ (k : K) (w : F), b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧ (∀ (v : F), v ∈ π.kFiniteSubspace K → ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)), b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by
-- proof
  obtain ⟨b, hb_ne, hb_comm, hb_orbit⟩ := casimir_exists_nonzero_kEquivariant I π K hG_ss hK_max
  exact ⟨b, hb_ne, hb_comm, fun v hv =>
    kEquivariant_preserves_kOrbitSpan π K b hb_comm v (hb_orbit v hv)⟩

end ContinuousRep

namespace ContinuousRep

/--
[exists_kInvariant_laplacian_endomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma exists_kInvariant_laplacian_endomorphism
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [Nontrivial F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
  {v : F}
-- given
  (hG_ss : IsSemisimpleLieGroup I G)
  (hK_max : IsMaximalCompactSubgroup K)
  (hv : v ∈ π.kFiniteSubspace K) :
-- imply
  ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧ ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)), b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
-- proof
  obtain ⟨b, hb_ne, _, hb_pres⟩ := casimir_exists_nonzero_kInvariant_aux I π K hG_ss hK_max
  exact ⟨b, hb_ne, hb_pres v hv⟩

end ContinuousRep

namespace ContinuousRep

/--
[orbit_map_smooth_of_kfinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma orbit_map_smooth_of_kfinite
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [SecondCountableTopology G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
  [T2Space K]
  {v : F}
-- given
  (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
  (hv : v ∈ π.kFiniteSubspace K) :
-- imply
  ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) :=
-- proof
admissible_kfinite_le_smooth I π K hadm hv

end ContinuousRep

namespace ContinuousRep

/--
[matrix_coeff_smooth_kfinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma matrix_coeff_smooth_kfinite
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [SecondCountableTopology G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
  [T2Space K]
  {v : F}
-- given
  (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
  (hv : v ∈ π.kFiniteSubspace K)
  (h : F →L[ℂ] ℂ) :
-- imply
  ContMDiff I 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞) (fun g : G => (h (π.toMonoidHom g v)).re) := by
-- proof
  have horbit : ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) :=
    orbit_map_smooth_of_kfinite I π K hadm v hv
  have hfun_eq : (fun g : G => (h (π.toMonoidHom g v)).re) =
    (fun z : ℂ => z.re) ∘ h ∘ (π.orbitMap v) := by
    ext g; rfl
  rw [hfun_eq]
  haveI : IsScalarTower ℝ ℂ F := ⟨fun r c x => by
    simp only [Complex.real_smul, mul_smul]; rfl⟩
  have hre_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞) (fun z : ℂ => z.re) :=
    Complex.reCLM.contMDiff.of_le le_top
  have hh_smooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ↑(⊤ : ℕ∞) (fun w : F => h w) :=
    ((h.restrictScalars ℝ).contDiff.contMDiff).of_le le_top
  exact hre_smooth.comp (hh_smooth.comp horbit)

end ContinuousRep

namespace ContinuousRep

/--
[laplacian_annihilates_matrix_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma laplacian_annihilates_matrix_coeff
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  [CompactSpace K]
  {b : F →ₗ[ℂ] F}
  {v : F}
  {P : Polynomial ℂ}
  {D : (G → ℝ) →ₗ[ℝ] (G → ℝ)}
-- given
  (_hG_ss : IsSemisimpleLieGroup I G)
  (_hK_max : IsMaximalCompactSubgroup K)
  (h : F →L[ℂ] ℂ)
  (hPv : ((Polynomial.aeval b) P) v = 0)
  (hD_compat : ∀ (v : F) (h : F →L[ℂ] ℂ) (x : G), D (fun g : G => (h (π.toMonoidHom g v)).re) x = (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) :
-- imply
  ∀ x : G, D (fun g : G => (h (π.toMonoidHom g v)).re) x = 0 := by
-- proof
  intro x
  rw [hD_compat v h x, hPv, map_zero, map_zero, Complex.zero_re]

end ContinuousRep

namespace ContinuousRep

/--
[restrictEndomorphism_pow_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma restrictEndomorphism_pow_coe
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {b : F →ₗ[ℂ] F}
  {W : Submodule ℂ F}
  {n : ℕ}
-- given
  (hb : ∀ w ∈ W, b w ∈ W) :
-- imply
  ∀ w : W, ((restrictEndomorphism b W hb ^ n) w : F) = (b ^ n) (w : F) := by
-- proof
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    show (((restrictEndomorphism b W hb ^ n) ((restrictEndomorphism b W hb) w)) : F) =
      (b ^ n) (b (w : F))
    rw [ih]; simp [restrictEndomorphism]

end ContinuousRep

namespace ContinuousRep

/--
[aeval_restrictEndomorphism_coe](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma aeval_restrictEndomorphism_coe
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {b : F →ₗ[ℂ] F}
  {W : Submodule ℂ F}
  {P : Polynomial ℂ}
  {w : W}
-- given
  (hb : ∀ w ∈ W, b w ∈ W) :
-- imply
  ((Polynomial.aeval (restrictEndomorphism b W hb) P) w : F) = (Polynomial.aeval b P) (w : F) := by
-- proof
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq, Submodule.coe_add]
  | monomial n c =>
    simp [Polynomial.aeval_monomial]
    show (c • ((restrictEndomorphism b W hb ^ n) w) : F) = c • ((b ^ n) (w : F))
    simp [restrictEndomorphism_pow_coe]

end ContinuousRep

namespace ContinuousRep

/--
[cayley_hamilton_annihilation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/AnalyticityRegularity.lean)
-/
@[path]
lemma cayley_hamilton_annihilation
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  {F : Type uFsec}
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {b : F →ₗ[ℂ] F}
  {W : Submodule ℂ F}
  [FiniteDimensional ℂ W]
  {v : F}
-- given
  (hb : ∀ w ∈ W, b w ∈ W)
  (hv : v ∈ W) :
-- imply
  ∃ P : Polynomial ℂ, P ≠ 0 ∧ ((Polynomial.aeval b) P) v = 0 := by
-- proof
  set b_W := restrictEndomorphism b W hb
  refine ⟨b_W.charpoly, ?_, ?_⟩
  ·
    exact ne_of_apply_ne Polynomial.leadingCoeff
      (by simp [b_W.charpoly_monic.leadingCoeff])
  ·
    have hCH := LinearMap.aeval_self_charpoly b_W
    have h0 : (((Polynomial.aeval b_W b_W.charpoly) ⟨v, hv⟩ : W) : F) = 0 := by
      simp [hCH]
    rwa [aeval_restrictEndomorphism_coe] at h0
end ContinuousRep



-- created on 2026-10-23
