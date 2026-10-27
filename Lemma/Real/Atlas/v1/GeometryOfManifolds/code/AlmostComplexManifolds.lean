import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
open DifferentialFormSpace SymplecticLinearAlgebra


/--
[polar_decomp_compatible_acs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma polar_decomp_compatible_acs
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [ht : HasTangentSpaces Ω VF]
  {S : SymplecticManifold Ω VF} :
-- imply
  ∃ J : AlmostComplexStr (inst := inst), IsCompatibleACS S J := by
-- proof
  have h_sympl : ∀ x : ht.M, IsSymplecticForm (ht.eval₂ x S.ω) :=
    ht.eval_is_symplectic S
  have h_pw : ∀ x : ht.M,
    ∃ Jx : ht.TangentSpaceAt x →ₗ[ℝ] ht.TangentSpaceAt x,
      IsCompatibleComplexStr (ht.eval₂ x S.ω) Jx :=
    fun x => exists_compatible_complex_structure (h_sympl x)
  let Jfam : ∀ x : ht.M, ht.TangentSpaceAt x →ₗ[ℝ] ht.TangentSpaceAt x :=
    fun x => (h_pw x).choose
  have hJfam : ∀ x, IsCompatibleComplexStr (ht.eval₂ x S.ω) (Jfam x) :=
    fun x => (h_pw x).choose_spec
  let J_global : VF → VF := ht.liftJ Jfam
  refine ⟨⟨J_global, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ht.lift_sq_neg Jfam (fun x => (hJfam x).complex_str)
  · exact ht.lift_preserves S Jfam (fun x u v => (hJfam x).preserves u v)
  · exact ht.lift_taming S Jfam (fun x v hv => (hJfam x).positive v hv)

/--
[polar_decomp_path_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma polar_decomp_path_zero
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {ω : LinearMap.BilinForm ℝ V}
  {J₀ J₁ : CompatibleComplexStructureSpace ω}
-- given
  (hω : IsSymplecticForm ω) :
-- imply
  polar_decomp_path hω J₀ J₁ ⟨0, le_refl _, zero_le_one⟩ = J₀ := by
-- proof
  simp only [polar_decomp_path]
  apply Subtype.ext
  simp
  exact (polar_decomposition_compatible_J hω).choose_spec.2 J₀.val J₀.property

/--
[polar_decomp_path_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma polar_decomp_path_one
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {ω : LinearMap.BilinForm ℝ V}
  {J₀ J₁ : CompatibleComplexStructureSpace ω}
-- given
  (hω : IsSymplecticForm ω) :
-- imply
  polar_decomp_path hω J₀ J₁ ⟨1, zero_le_one, le_refl _⟩ = J₁ := by
-- proof
  simp only [polar_decomp_path]
  apply Subtype.ext
  simp
  exact (polar_decomposition_compatible_J hω).choose_spec.2 J₁.val J₁.property

/--
[compatible_forms_convex_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma compatible_forms_convex_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S₀ S₁ : SymplecticManifold Ω VF}
  {t : ℝ} :
-- imply
  inst.d ((1 - t) • S₀.ω + t • S₁.ω) = 0 := by
-- proof
  rw [inst.d_add, inst.d_smul, inst.d_smul, S₀.closed, S₁.closed,
    smul_zero, smul_zero, add_zero]

/--
[compatible_forms_convex_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma compatible_forms_convex_compat
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {S₀ S₁ : SymplecticManifold Ω VF}
  {t : ℝ}
-- given
  (J : AlmostComplexStr (inst := inst))
  (h₀ : IsCompatibleACS S₀ J)
  (h₁ : IsCompatibleACS S₁ J) :
-- imply
  ∀ (u v : VF), inst.ι (J.J u) (inst.ι (J.J v) ((1 - t) • S₀.ω + t • S₁.ω)) = inst.ι u (inst.ι v ((1 - t) • S₀.ω + t • S₁.ω)) := by
-- proof
  intro u v
  simp only [inst.ι_add, inst.ι_smul]
  rw [h₀.preserves u v, h₁.preserves u v]

/--
[ι_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma ι_neg {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
  (X : VF) {p : ℕ} (α : Ω (p + 1)) :
  inst.ι X (-α) = -(inst.ι X α) := by
  have h := inst.ι_smul X (-1 : ℝ) α
  simp only [neg_one_smul] at h; exact h

/--
[ι_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma ι_sub {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
  (X : VF) {p : ℕ} (α β : Ω (p + 1)) :
  inst.ι X (α - β) = inst.ι X α - inst.ι X β := by
  rw [sub_eq_add_neg, inst.ι_add, ι_neg, ← sub_eq_add_neg]

/--
[compatible_forms_convex_nondeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma compatible_forms_convex_nondeg
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hp : HasPositivity (Ω 0)]
  {S₀ S₁ : SymplecticManifold Ω VF}
  {t : ℝ}
-- given
  (J : AlmostComplexStr (inst := inst))
  (ht₀ : IsTaming S₀ J)
  (ht₁ : IsTaming S₁ J)
  (ht : t ∈ Set.Icc 0 1) :
-- imply
  Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • S₀.ω + t • S₁.ω)) := by
-- proof
  intro X Y hXY
  by_contra hne
  have hdiff : (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
    t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) = (0 : Ω 1) := by
    have h_sub : inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
      inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω) = 0 :=
      sub_eq_zero.mpr hXY
    simp only [inst.ι_add, inst.ι_smul] at h_sub
    have h_eq : (1 - t) • inst.ι X S₀.ω + t • inst.ι X S₁.ω =
      (1 - t) • inst.ι Y S₀.ω + t • inst.ι Y S₁.ω :=
      sub_eq_zero.mp h_sub
    have h_rearr : (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
      t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) =
      ((1 - t) • inst.ι X S₀.ω + t • inst.ι X S₁.ω) -
      ((1 - t) • inst.ι Y S₀.ω + t • inst.ι Y S₁.ω) := by
      simp only [smul_sub]; abel
    rw [h_rearr, h_eq, sub_self]
  have heval : inst.ι (J.J X) ((1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
    t • (inst.ι X S₁.ω - inst.ι Y S₁.ω)) = (0 : Ω 0) := by
    rw [hdiff]; exact ι_zero_val _
  rw [inst.ι_add, inst.ι_smul, inst.ι_smul] at heval
  have pos₀ := ht₀.taming X Y hne
  have pos₁ := ht₁.taming X Y hne
  obtain ⟨h0, h1⟩ := ht
  by_cases ht0 : t = 0
  ·
    subst ht0; simp only [sub_zero, one_smul, zero_smul, add_zero] at heval
    exact hp.pos_nonzero _ pos₀ heval
  by_cases ht1 : t = 1
  ·
    subst ht1; simp only [sub_self, zero_smul, one_smul, zero_add] at heval
    exact hp.pos_nonzero _ pos₁ heval
  ·
    have ht_pos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
    have h1t_pos : 0 < 1 - t := by
      have : t < 1 := lt_of_le_of_ne h1 ht1
      linarith
    have hpos_sum := hp.pos_add _ _
      (hp.pos_smul_pos _ _ h1t_pos pos₀)
      (hp.pos_smul_pos _ _ ht_pos pos₁)
    exact hp.pos_nonzero _ hpos_sum heval

/--
[compatible_forms_convex_taming](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma compatible_forms_convex_taming
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hp : HasPositivity (Ω 0)]
  {S₀ S₁ : SymplecticManifold Ω VF}
  {t : ℝ}
-- given
  (J : AlmostComplexStr (inst := inst))
  (ht₀ : IsTaming S₀ J)
  (ht₁ : IsTaming S₁ J)
  (ht : t ∈ Set.Icc 0 1) :
-- imply
  IsTaming (⟨(1 - t) • S₀.ω + t • S₁.ω, compatible_forms_convex_closed S₀ S₁ t, compatible_forms_convex_nondeg J S₀ S₁ ht₀ ht₁ t ht⟩ : SymplecticManifold Ω VF) J := by
-- proof
  constructor
  intro X Y hne
  show hp.IsPositive (inst.ι (J.J X) (inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
    inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω)))
  have hexpand : inst.ι X ((1 - t) • S₀.ω + t • S₁.ω) -
    inst.ι Y ((1 - t) • S₀.ω + t • S₁.ω) =
    (1 - t) • (inst.ι X S₀.ω - inst.ι Y S₀.ω) +
    t • (inst.ι X S₁.ω - inst.ι Y S₁.ω) := by
    simp only [inst.ι_add, inst.ι_smul, smul_sub]; abel
  rw [hexpand, inst.ι_add, inst.ι_smul, inst.ι_smul]
  have pos₀ := ht₀.taming X Y hne
  have pos₁ := ht₁.taming X Y hne
  obtain ⟨h0, h1⟩ := ht
  by_cases ht0 : t = 0
  · subst ht0; simp only [sub_zero, one_smul, zero_smul, add_zero]; exact pos₀
  by_cases ht1 : t = 1
  · subst ht1; simp only [sub_self, zero_smul, one_smul, zero_add]; exact pos₁
  · have ht_pos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
    have h1t_pos : 0 < 1 - t := by linarith [lt_of_le_of_ne h1 ht1]
    exact hp.pos_add _ _ (hp.pos_smul_pos _ _ h1t_pos pos₀) (hp.pos_smul_pos _ _ ht_pos pos₁)

/--
[DFSMorphism.pullback_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma DFSMorphism.pullback_zero'
  {Ω_M : ℕ → Type*}
  {Ω_X : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω_M VF_M}
  {p : ℕ} :
-- imply
  i.pullback (0 : Ω_M p) = 0 := by
-- proof
  have := i.pullback_smul (0 : ℝ) (0 : Ω_M p)
  simp only [zero_smul] at this; exact this

/--
[DFSMorphism.pullback_closed'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma DFSMorphism.pullback_closed'
  {Ω_M : ℕ → Type*}
  {Ω_X : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω_M VF_M}
  {p : ℕ}
  {α : Ω_M p}
-- given
  (hclosed : inst_M.d α = 0) :
-- imply
  inst_X.d (i.pullback α) = 0 := by
-- proof
  rw [← i.pullback_comm_d, hclosed, i.pullback_zero']

/--
[DFSMorphism.pullback_sub'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma DFSMorphism.pullback_sub'
  {Ω_M : ℕ → Type*}
  {Ω_X : ℕ → Type*}
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω_M VF_M}
  {p : ℕ}
  {α β : Ω_M p} :
-- imply
  i.pullback (α - β) = i.pullback α - i.pullback β := by
-- proof
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [show (-β : Ω_M p) = (-1 : ℝ) • β from by simp only [neg_one_smul]]
  rw [i.pullback_add, i.pullback_smul]
  simp only [neg_one_smul]

/--
[acs_submanifold_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
lemma acs_submanifold_symplectic
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ω : PointwiseSymplecticForm I M}
  {J : AlmostComplexStructure I M}
  {x : M}
  {W : Submodule ℝ (TangentSpace I x)}
-- given
  (hcompat : IsCompatibleACS_Mathlib I M ω J)
  (hJ_inv : ∀ v ∈ W, (J.J x) v ∈ W) :
-- imply
  ∀ v ∈ W, v ≠ 0 → ∃ w ∈ W, ω.form x v w ≠ 0 := by
-- proof
  intro v hv hv_ne
  have hJv : (J.J x) v ∈ W := hJ_inv v hv
  have h_pos := hcompat.taming x v hv_ne
  exact ⟨(J.J x) v, hJv, ne_of_gt h_pos⟩
section Integrability_Mathlib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
[compRight_injective_of_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
private lemma compRight_injective_of_symplectic_eq
  [AddCommGroup V]
  [Module ℝ V]
  {ω : LinearMap.BilinForm ℝ V}
  {J₁ J₂ : V →ₗ[ℝ] V}
-- given
  (hω : IsSymplecticForm ω)
  (h : ω.compRight J₁ = ω.compRight J₂) :
-- imply
  J₁ = J₂ := by
-- proof
  apply compRight_injective_of_symplectic hω h

/--
[polar_decomposition_compatible_J](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
private lemma polar_decomposition_compatible_J_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {ω : LinearMap.BilinForm ℝ V}
-- given
  (hω : IsSymplecticForm ω) :
-- imply
  ∃ (polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V), (∀ g, IsCompatibleComplexStr ω (polar g)) ∧ (∀ (J : V →ₗ[ℝ] V), IsCompatibleComplexStr ω J → polar (ω.compRight J) = J) := by
-- proof
  apply polar_decomposition_compatible_J hω

/--
[pointwise_form_is_symplectic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean)
-/
@[path]
private lemma pointwise_form_is_symplectic_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {ω : PointwiseSymplecticForm I M}
  {x : M} :
-- imply
  IsSymplecticForm (ω.form x) := by
-- proof
  apply pointwise_form_is_symplectic ω x


-- created on 2026-10-23
