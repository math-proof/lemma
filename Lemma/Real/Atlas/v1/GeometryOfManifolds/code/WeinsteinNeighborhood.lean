import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part7
open Module FiniteDimensional SymplecticLinearAlgebra DifferentialFormSpace WeinsteinNeighborhood
open SymplecticLinearAlgebra
open DifferentialFormSpace


/--
[cohomology_isomorphism_surjectivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma cohomology_isomorphism_surjectivity
  {Ω_X : ℕ → Type*}
  {Ω_U : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_U : DifferentialFormSpace Ω_U VF_U]
  {i : DFSMorphism Ω_X VF_X Ω_U VF_U}
  {π : DFSMorphism Ω_U VF_U Ω_X VF_X}
-- given
  (h_retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α) :
-- imply
  ∀ {p : ℕ} (α : Ω_X p), ∃ (β : Ω_U p), i.pullback β = α :=
-- proof
  fun α => ⟨π.pullback α, h_retraction α⟩

/--
[HasTubularHomotopyPrimitives.Φ_preserves_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma HasTubularHomotopyPrimitives.Φ_preserves_vanishing
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω VF}
  {p : ℕ}
  {γ : Ω p}
-- given
  (hp : HasTubularHomotopyPrimitives Ω VF Ω_X VF_X i)
  (hγ : i.pullback γ = 0) :
-- imply
  i.pullback (hp.Φ γ) = 0 := by
-- proof
  rw [hp.Φ_fix_X γ, hγ]

/--
[relative_poincare_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma relative_poincare_lemma
  {Ω_U : ℕ → Type*}
  [inst_U : DifferentialFormSpace Ω_U VF_U]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω_U VF_U}
  {ℓ : ℕ}
  {β : Ω_U (ℓ + 1)}
-- given
  (hK : HasRelativeHomotopyOperator Ω_U VF_U Ω_X VF_X i)
  (hclosed : inst_U.d β = 0)
  (hvanish : i.pullback β = 0) :
-- imply
  ∃ (μ : Ω_U ℓ), inst_U.d μ = β ∧ i.pullback μ = 0 := by
-- proof
  refine ⟨hK.K β, ?_, hK.K_vanishes_on_X β⟩
  have hformula := hK.homotopy_formula β
  have hK_zero : hK.K (inst_U.d β) = (0 : Ω_U (ℓ + 1)) := by
    rw [hclosed]
    have := hK.K_smul (0 : ℝ) (0 : Ω_U (ℓ + 1 + 1))
    simp [zero_smul] at this
    exact this
  have hpull_zero : hK.π.pullback (i.pullback β) = (0 : Ω_U (ℓ + 1)) := by
    rw [hvanish]
    have := hK.π.pullback_smul (0 : ℝ) (0 : Ω_X (ℓ + 1))
    simp [zero_smul] at this
    exact this
  rwa [hK_zero, hpull_zero, add_zero, sub_zero] at hformula

/--
[relative_poincare_lemma_from_primitives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma relative_poincare_lemma_from_primitives
  {Ω_U : ℕ → Type*}
  [inst_U : DifferentialFormSpace Ω_U VF_U]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω_U VF_U}
  {ℓ : ℕ}
  {β : Ω_U (ℓ + 1)}
-- given
  (hp : HasTubularHomotopyPrimitives Ω_U VF_U Ω_X VF_X i)
  (hclosed : inst_U.d β = 0)
  (hvanish : i.pullback β = 0) :
-- imply
  ∃ (μ : Ω_U ℓ), inst_U.d μ = β ∧ i.pullback μ = 0 := by
-- proof
  set μ := hp.Φ (inst_U.ι hp.V β)
  refine ⟨μ, ?_, ?_⟩
  ·
    have homotopy : inst_U.d μ + hp.Φ (inst_U.ι hp.V (inst_U.d β)) =
      β - hp.π.pullback (i.pullback β) :=
      homotopy_formula_from_cartan_and_ftc i hp.π hp.V hp.Φ
        (fun β => hp.Φ (inst_U.ι hp.V β))
        (fun _ => rfl) hp.Φ_add hp.Φ_d hp.Φ_FTC β
    have hK_dβ : hp.Φ (inst_U.ι hp.V (inst_U.d β)) = (0 : Ω_U (ℓ + 1)) := by
      rw [hclosed]
      have h1 : inst_U.ι hp.V (0 : Ω_U (ℓ + 1 + 1)) = (0 : Ω_U (ℓ + 1)) := by
        have := inst_U.ι_smul hp.V (0 : ℝ) (0 : Ω_U (ℓ + 1 + 1))
        simp [zero_smul] at this; exact this
      rw [h1]
      have h2 := hp.Φ_smul (0 : ℝ) (0 : Ω_U (ℓ + 1))
      simp [zero_smul] at h2; exact h2
    have hpull_zero : hp.π.pullback (i.pullback β) = (0 : Ω_U (ℓ + 1)) := by
      rw [hvanish]
      have := hp.π.pullback_smul (0 : ℝ) (0 : Ω_X (ℓ + 1))
      simp [zero_smul] at this; exact this
    rwa [hK_dβ, hpull_zero, add_zero, sub_zero] at homotopy
  ·
    exact K_vanishes_on_X_from_axioms i hp.V hp.Φ
      hp.ιV_vanish_on_X hp.Φ_preserves_vanishing β

/--
[relative_poincare_lemma_of_retract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma relative_poincare_lemma_of_retract
  {Ω_X : ℕ → Type*}
  {Ω_U : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_U : DifferentialFormSpace Ω_U VF_U]
  {i : DFSMorphism Ω_X VF_X Ω_U VF_U}
  {ℓ : ℕ}
  {β : Ω_U (ℓ + 1)}
-- given
  (hdr : HasDeformationRetract i)
  (hclosed : inst_U.d β = 0)
  (hvanish : i.pullback β = 0) :
-- imply
  ∃ (μ : Ω_U ℓ), inst_U.d μ = β ∧ i.pullback μ = 0 := by
-- proof
  refine ⟨hdr.K β, ?_, hdr.K_vanishes_on_X β⟩
  have hformula := hdr.homotopy_formula β
  have hK_zero : hdr.K (inst_U.d β) = (0 : Ω_U (ℓ + 1)) := by
    rw [hclosed]
    have := hdr.K_smul (0 : ℝ) (0 : Ω_U (ℓ + 1 + 1))
    simp [zero_smul] at this
    exact this
  have hpull_zero : hdr.π.pullback (i.pullback β) = (0 : Ω_U (ℓ + 1)) := by
    rw [hvanish]
    have := hdr.π.pullback_smul (0 : ℝ) (0 : Ω_X (ℓ + 1))
    simp [zero_smul] at this
    exact this
  rwa [hK_zero, hpull_zero, add_zero, sub_zero] at hformula

/--
[cohomology_isomorphism_injectivity_of_retract](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma cohomology_isomorphism_injectivity_of_retract
  {Ω_X : ℕ → Type*}
  {Ω_U : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_U : DifferentialFormSpace Ω_U VF_U]
  {i : DFSMorphism Ω_X VF_X Ω_U VF_U}
-- given
  (hdr : HasDeformationRetract i) :
-- imply
  ∀ (p : ℕ) (β : Ω_U (p + 1)), inst_U.d β = 0 → (∃ (γ : Ω_X p), i.pullback β = inst_X.d γ) → ∃ (η : Ω_U p), β = inst_U.d η := by
-- proof
  intro p β hclosed ⟨γ, hγ⟩
  set dπγ := inst_U.d (hdr.π.pullback γ)
  set β' := β - dπγ with hβ'_def
  have hβ'_closed : inst_U.d β' = 0 := by
    have hsub : β' = β + (-1 : ℝ) • dπγ := by
      rw [hβ'_def, sub_eq_add_neg, neg_one_smul]
    rw [hsub, inst_U.d_add, inst_U.d_smul, inst_U.d_squared, smul_zero, add_zero, hclosed]
  have hβ'_vanish : i.pullback β' = 0 := by
    have hsub : β' = β + (-1 : ℝ) • dπγ := by
      rw [hβ'_def, sub_eq_add_neg, neg_one_smul]
    rw [hsub, i.pullback_add, i.pullback_smul, i.pullback_comm_d,
      hdr.retraction γ, hγ]
    simp
  obtain ⟨μ, hμ, _⟩ := relative_poincare_lemma_of_retract i hdr β' hβ'_closed hβ'_vanish
  exact ⟨μ + hdr.π.pullback γ, by rw [inst_U.d_add, hμ, hβ'_def, sub_add_cancel]⟩

/--
[cohomology_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma cohomology_isomorphism
  {Ω_X : ℕ → Type*}
  {Ω_U₁ : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁]
  {i : DFSMorphism Ω_X VF_X Ω_U₁ VF_U₁}
-- given
  (hdr : HasDeformationRetract i) :
-- imply
  (∀ {p : ℕ} (α : Ω_X p), ∃ (β : Ω_U₁ p), i.pullback β = α) ∧ (∀ (p : ℕ) (β : Ω_U₁ (p + 1)), inst_U₁.d β = 0 → (∃ (γ : Ω_X p), i.pullback β = inst_X.d γ) → ∃ (η : Ω_U₁ p), β = inst_U₁.d η) ∧ (∀ (β : Ω_U₁ 0), inst_U₁.d β = (0 : Ω_U₁ 1) → i.pullback β = (0 : Ω_X 0) → β = (0 : Ω_U₁ 0)) :=
-- proof
  ⟨cohomology_isomorphism_surjectivity i hdr.π hdr.retraction,
    cohomology_isomorphism_injectivity_of_retract i hdr,
    hdr.deg0_injectivity⟩

/--
[moser_cartan_computation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma moser_cartan_computation
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {v : VF}
  {ω : Ω 2}
  {μ : Ω 1}
-- given
  (hω_closed : inst.d ω = 0)
  (hι : inst.ι v ω = -μ) :
-- imply
  inst.L v ω = -(inst.d μ) := by
-- proof
  have hcartan := cartan_formula v ω
  rw [hcartan]
  rw [hω_closed, DifferentialFormSpace.ι_zero_val]
  rw [hι, DifferentialFormSpace.d_neg]
  simp [add_zero]

/--
[moser_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma moser_cancellation
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {v : VF}
  {ω : Ω 2}
  {μ : Ω 1}
  {σ : Ω 2}
-- given
  (hω_closed : inst.d ω = 0)
  (hι : inst.ι v ω = -μ)
  (hdμ : inst.d μ = σ) :
-- imply
  inst.L v ω + σ = 0 := by
-- proof
  have h := moser_cartan_computation v ω μ hω_closed hι
  rw [h, hdμ]
  simp [neg_add_cancel]

/--
[moser_difference_closed_and_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma moser_difference_closed_and_vanishes
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω VF}
  {ω₀ ω₁ : Ω 2}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (hagree : i.pullback ω₀ = i.pullback ω₁) :
-- imply
  inst.d (ω₁ - ω₀) = 0 ∧ i.pullback (ω₁ - ω₀) = 0 := by
-- proof
  constructor
  ·
    rw [show ω₁ - ω₀ = ω₁ + (-ω₀) from sub_eq_add_neg _ _]
    rw [inst.d_add ω₁ (-ω₀)]
    rw [show inst.d (-ω₀) = -(inst.d ω₀) from by
      have := inst.d_smul (-1 : ℝ) ω₀; simp at this; exact this]
    rw [hclosed₀, hclosed₁]; simp
  ·
    rw [show ω₁ - ω₀ = ω₁ + (-ω₀) from sub_eq_add_neg _ _]
    rw [i.pullback_add]
    rw [show i.pullback (-ω₀) = -(i.pullback ω₀) from by
      have := i.pullback_smul (-1 : ℝ) ω₀; simp at this; exact this]
    rw [hagree, add_neg_cancel]

/--
[moser_interpolation_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma moser_interpolation_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {ω₀ ω₁ : Ω 2}
  {t : ℝ}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0) :
-- imply
  inst.d ((1 - t) • ω₀ + t • ω₁) = 0 :=
-- proof
  interpolating_closed ω₀ ω₁ hclosed₀ hclosed₁ t

/--
[moser_equation_solvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma moser_equation_solvable
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {ω : Ω 2}
  {μ : Ω 1}
-- given
  (hsurj : @ContractionSurjective Ω VF inst ω) :
-- imply
  ∃ (v : VF), inst.ι v ω = -μ :=
-- proof
  hsurj (-μ)

/--
[local_moser_diffeomorphism_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma local_moser_diffeomorphism_core
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω VF}
  {ω₀ ω₁ : Ω 2}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (_hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
  (_hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
  (_hagree : ∀ (V : VF), i.pullback (inst.ι V ω₀) = i.pullback (inst.ι V ω₁))
  (h_homotopy_op : HasRelativeHomotopyOperator Ω VF Ω_X VF_X i)
  (h_pb_agree : (∀ (V : VF), i.pullback (inst.ι V ω₀) = i.pullback (inst.ι V ω₁)) → i.pullback ω₀ = i.pullback ω₁)
  (h_contr_surj : Function.Injective (fun X => inst.ι X ω₀) → @ContractionSurjective Ω VF inst ω₀)
  (h_ode_flow : ∀ (μ : Ω 1) (v : VF), inst.d μ = ω₁ - ω₀ → i.pullback μ = 0 → inst.ι v ω₀ = -μ → inst.L v ω₀ + (ω₁ - ω₀) = 0 → ∃ (φ : DFSMorphism Ω VF Ω VF) (φ_inv : DFSMorphism Ω VF Ω VF), φ.pullback ω₁ = ω₀ ∧ (∀ {p : ℕ} (α : Ω p), φ_inv.pullback (φ.pullback α) = α) ∧ (∀ {p : ℕ} (α : Ω p), φ.pullback (φ_inv.pullback α) = α) ∧ (∀ {p : ℕ} (α : Ω p), i.pullback (φ.pullback α) = i.pullback α)) :
-- imply
  ∃ (φ : DFSMorphism Ω VF Ω VF) (φ_inv : DFSMorphism Ω VF Ω VF), φ.pullback ω₁ = ω₀ ∧ (∀ {p : ℕ} (α : Ω p), φ_inv.pullback (φ.pullback α) = α) ∧ (∀ {p : ℕ} (α : Ω p), φ.pullback (φ_inv.pullback α) = α) ∧ (∀ {p : ℕ} (α : Ω p), i.pullback (φ.pullback α) = i.pullback α) := by
-- proof
  have hτ := h_homotopy_op
  have hagree_pb : i.pullback ω₀ = i.pullback ω₁ :=
    h_pb_agree _hagree
  have hnd_surj : @ContractionSurjective Ω VF inst ω₀ :=
    h_contr_surj _hnd₀
  have ⟨hσ_closed, hσ_vanish⟩ :=
    moser_difference_closed_and_vanishes i ω₀ ω₁ hclosed₀ hclosed₁ hagree_pb
  have hPoincare := @relative_poincare_lemma Ω VF inst Ω_X VF_X inst_X i hτ 1 (ω₁ - ω₀)
    (by
      have : ω₁ - ω₀ = ω₁ + (-ω₀) := sub_eq_add_neg ω₁ ω₀
      rw [this, inst.d_add, DifferentialFormSpace.d_neg, hclosed₀, hclosed₁]; simp)
    (by
      have hsub : ω₁ - ω₀ = ω₁ + (-ω₀) := sub_eq_add_neg ω₁ ω₀
      rw [hsub, i.pullback_add]
      have hneg : i.pullback (-ω₀) = -(i.pullback ω₀) := by
        have := i.pullback_smul (-1 : ℝ) ω₀; simp at this; exact this
      rw [hneg, hagree_pb, add_neg_cancel])
  obtain ⟨μ, hdμ, hμ_vanishes⟩ := hPoincare
  have _hωt_closed : ∀ t : ℝ, inst.d ((1 - t) • ω₀ + t • ω₁) = 0 :=
    fun t => moser_interpolation_closed ω₀ ω₁ hclosed₀ hclosed₁ t
  obtain ⟨v, hv⟩ := moser_equation_solvable ω₀ μ hnd_surj
  have hcancel := moser_cancellation v ω₀ μ (ω₁ - ω₀) hclosed₀ hv hdμ
  exact h_ode_flow μ v hdμ hμ_vanishes hv hcancel
universe u_Ω u_VF

/--
[weinstein_lagrangian_neighborhood_core_from_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma weinstein_lagrangian_neighborhood_core_from_data
  {Ω_X : ℕ → Type*}
  {Ω_M : ℕ → Type*}
  {Ω_TX : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  [inst_M : DifferentialFormSpace Ω_M VF_M]
  [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
  [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
  {S_M : SymplecticManifold Ω_M VF_M}
  {i : DFSMorphism Ω_X VF_X Ω_M VF_M}
-- given
  (_hClosed : IsClosedSubmanifold i)
  (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX)
  (hTub : HasLagrangianTubularData S_M i hLag) :
-- imply
  let inst_U := hTub.inst_U let inst_V := hTub.inst_V let S_U₀ : @SymplecticManifold hTub.Ω_U hTub.VF_U inst_U := ⟨hTub.ω₀, hTub.hclosed₀, hTub.hnd₀⟩ ∃ (Φ : @Symplectomorphism hTub.Ω_U hTub.VF_U hTub.Ω_V hTub.VF_V inst_U inst_V S_U₀ hTub.S_V), ∀ {p : ℕ} (α : hTub.Ω_V p), hTub.j.pullback (Φ.toMorphism.pullback α) = hTub.j_V.pullback α := by
-- proof
  letI inst_U := hTub.inst_U
  letI inst_V := hTub.inst_V
  let φ := hTub.φ
  let φ_inv := hTub.φ_inv
  let ψφ := @DFSMorphism.comp hTub.Ω_U hTub.VF_U hTub.Ω_U hTub.VF_U
    hTub.Ω_V hTub.VF_V inst_U inst_U inst_V hTub.ψ φ
  have hψφ_eq : ∀ {p : ℕ} (α : hTub.Ω_V p),
    ψφ.pullback α = φ.pullback (hTub.ψ.pullback α) :=
    fun _ => rfl
  let φ_inv_ψ_inv := @DFSMorphism.comp hTub.Ω_V hTub.VF_V hTub.Ω_U hTub.VF_U
    hTub.Ω_U hTub.VF_U inst_V inst_U inst_U φ_inv hTub.ψ_inv
  have hφ_inv_ψ_inv_eq : ∀ {p : ℕ} (α : hTub.Ω_U p),
    φ_inv_ψ_inv.pullback α = hTub.ψ_inv.pullback (φ_inv.pullback α) :=
    fun _ => rfl
  refine ⟨{
    toMorphism := ψφ
    invMorphism := φ_inv_ψ_inv
    left_inv := fun {p} α => by
      rw [hψφ_eq]
      rw [hφ_inv_ψ_inv_eq]
      rw [hTub.hφ_left]
      exact hTub.ψ_left α
    right_inv := fun {p} α => by
      rw [hφ_inv_ψ_inv_eq]
      rw [hψφ_eq]
      rw [hTub.ψ_right]
      exact hTub.hφ_right α
    pullback_symplectic := by
      show ψφ.pullback hTub.S_V.ω = hTub.ω₀
      rw [hψφ_eq, hTub.hω₁, hTub.hφ_pull]
  }, ?_⟩
  intro p α
  show hTub.j.pullback (ψφ.pullback α) = hTub.j_V.pullback α
  rw [hψφ_eq, hTub.hφ_id_X, hTub.hψ_X]

/--
[weinstein_and_H1_give_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma weinstein_and_H1_give_primitive
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace HH]
  {I : ModelWithCorners ℝ E HH}
  {M : Type*}
  [TopologicalSpace M]
  [ChartedSpace HH M]
  [IsManifold I ⊤ M]
  {X : Type*}
  [TopologicalSpace X]
  [ChartedSpace HH X]
  [IsManifold I ⊤ X]
  {i : X → M}
  {Y : C1CloseSubmanifold_mfld I M X i}
-- given
  (hLag : IsLagrangianEmbedding_mfld I M X i)
  (hH1 : HasVanishingH1_mfld I X) :
-- imply
  ∃ (h : X → ℝ), ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h ∧ (∀ x : X, Y.isIntersectionPt x ↔ mfderiv I (modelWithCornersSelf ℝ ℝ) h x = 0) :=
-- proof
  ⟨Y.h, Y.h_smooth, Y.crit_iff_intersection⟩

/--
[lagrangian_intersection_c1_close_Mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
lemma lagrangian_intersection_c1_close_Mathlib
  {E : Type*}
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  {X : Type*}
  [TopologicalSpace X]
  [CompactSpace X]
  {Y : C1CloseLagrangian_Mathlib E X}
-- given
  (hH1 : HasH1Vanishing_Mathlib E)
  (hEVT : ∀ (f : E → E [⋀^Fin 0]→L[ℝ] ℝ), ∃ x y : X, x ≠ y ∧ extDeriv f (Y.chart x) = 0 ∧ extDeriv f (Y.chart y) = 0) :
-- imply
  ∃ x y : X, x ≠ y ∧ Y.isZeroAt x ∧ Y.isZeroAt y := by
-- proof
  obtain ⟨f, hf⟩ := hH1.exact_of_closed Y.μ Y.μ_closed
  obtain ⟨x, y, hxy, hx_crit, hy_crit⟩ := hEVT f
  refine ⟨x, y, hxy, ?_, ?_⟩
  · rw [Y.zero_iff]
    have : Y.μ (Y.chart x) = extDeriv f (Y.chart x) := (hf (Y.chart x)).symm
    rw [this, hx_crit]
  · rw [Y.zero_iff]
    have : Y.μ (Y.chart y) = extDeriv f (Y.chart y) := (hf (Y.chart y)).symm
    rw [this, hy_crit]

/--
[symplecticToDual_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma symplecticToDual_ker_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  LinearMap.ker (symplecticToDual Ω E) = symplecticOrtho Ω E := by
-- proof
  apply WeinsteinNeighborhood.symplecticToDual_ker hΩ E

/--
[lagrangian_le_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma lagrangian_le_ker_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hE : IsLagrangian Ω E) :
-- imply
  E ≤ LinearMap.ker (symplecticToDual Ω E) := by
-- proof
  apply WeinsteinNeighborhood.lagrangian_le_ker hΩ hE

/--
[quotientToDual_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma quotientToDual_injective_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hE : IsLagrangian Ω E) :
-- imply
  Function.Injective (quotientToDual hΩ hE) := by
-- proof
  apply WeinsteinNeighborhood.quotientToDual_injective hΩ hE

/--
[quotient_finrank_eq_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma quotient_finrank_eq_dual_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hE : IsLagrangian Ω E) :
-- imply
  finrank ℝ (V ⧸ E) = finrank ℝ (Dual ℝ E) := by
-- proof
  apply WeinsteinNeighborhood.quotient_finrank_eq_dual hΩ hE

/--
[cartan_for_scaling_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma cartan_for_scaling_field_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {V : VF}
  {p : ℕ}
  {β : Ω (p + 1)} :
-- imply
  inst.d (inst.ι V β) + inst.ι V (inst.d β) = inst.L V β := by
-- proof
  apply cartan_for_scaling_field V β

/--
[homotopy_formula_from_cartan_and_ftc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma homotopy_formula_from_cartan_and_ftc_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_X : ℕ → Type*}
  [inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω VF}
  {π : DFSMorphism Ω VF Ω_X VF_X}
  {V : VF}
  {p : ℕ}
  {β : Ω (p + 1)}
-- given
  (Φ : ∀ {p : ℕ}, Ω p → Ω p)
  (K : ∀ {p : ℕ}, Ω (p + 1) → Ω p)
  (hK_def : ∀ {p : ℕ} (β : Ω (p + 1)), K β = Φ (inst.ι V β))
  (hΦ_add : ∀ {p : ℕ} (γ₁ γ₂ : Ω p), Φ (γ₁ + γ₂) = Φ γ₁ + Φ γ₂)
  (hΦ_d : ∀ {p : ℕ} (γ : Ω p), inst.d (Φ γ) = Φ (inst.d γ))
  (hFTC : ∀ {p : ℕ} (β : Ω (p + 1)), Φ (inst.L V β) = β - π.pullback (i.pullback β)) :
-- imply
  inst.d (K β) + K (inst.d β) = β - π.pullback (i.pullback β) := by
-- proof
  apply homotopy_formula_from_cartan_and_ftc i π V Φ K hK_def hΦ_add hΦ_d hFTC β

/--
[K_smul_from_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma K_smul_from_axioms_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {V : VF}
  {p : ℕ}
  {r : ℝ}
  {α : Ω (p + 1)}
-- given
  (Φ : ∀ {p : ℕ}, Ω p → Ω p)
  (hΦ_smul : ∀ {p : ℕ} (r : ℝ) (γ : Ω p), Φ (r • γ) = r • Φ γ) :
-- imply
  Φ (inst.ι V (r • α)) = r • Φ (inst.ι V α) := by
-- proof
  apply K_smul_from_axioms V Φ hΦ_smul r α

/--
[K_vanishes_on_X_from_axioms](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean)
-/
@[path]
private lemma K_vanishes_on_X_from_axioms_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {Ω_X : ℕ → Type*}
  [_inst_X : DifferentialFormSpace Ω_X VF_X]
  {i : DFSMorphism Ω_X VF_X Ω VF}
  {V : VF}
  {p : ℕ}
  {β : Ω (p + 1)}
-- given
  (Φ : ∀ {p : ℕ}, Ω p → Ω p)
  (hιV_vanish : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (inst.ι V β) = 0)
  (hΦ_preserve : ∀ {p : ℕ} (γ : Ω p), i.pullback γ = 0 → i.pullback (Φ γ) = 0) :
-- imply
  i.pullback (Φ (inst.ι V β)) = 0 := by
-- proof
  apply K_vanishes_on_X_from_axioms i V Φ hιV_vanish hΦ_preserve β


-- created on 2026-10-23
