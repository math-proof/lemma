import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.MoserDarboux
open Module FiniteDimensional Finset SymplecticLinearAlgebra DifferentialFormSpace
open SymplecticLinearAlgebra
open DifferentialFormSpace


/--
[stdSymplForm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma stdSymplForm_apply
  {n : ℕ}
  {u v : (Fin n → ℝ) × (Fin n → ℝ)} :
-- imply
  stdSymplForm n u v = ∑ i : Fin n, (u.1 i * v.2 i - v.1 i * u.2 i) := by
-- proof
  simp [stdSymplForm, LinearMap.mk₂_apply]

/--
[stdSymplForm_alt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma stdSymplForm_alt
  {n : ℕ} :
-- imply
  (stdSymplForm n).IsAlt := by
-- proof
  intro v
  show ∑ i : Fin n, (v.1 i * v.2 i - v.1 i * v.2 i) = 0
  simp

/--
[stdSymplForm_separatingLeft](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma stdSymplForm_separatingLeft
  {n : ℕ} :
-- imply
  (stdSymplForm n).SeparatingLeft := by
-- proof
  intro x hx
  have h1 : ∀ i : Fin n, x.1 i = 0 := by
    intro i
    have h := hx (0, Function.update 0 i 1)
    rw [stdSymplForm_apply] at h
    simp only [Pi.zero_apply, zero_mul, sub_zero] at h
    simpa [Finset.sum_ite_eq', Function.update_apply] using h
  have h2 : ∀ i : Fin n, x.2 i = 0 := by
    intro i
    have h := hx (Function.update 0 i 1, 0)
    rw [stdSymplForm_apply] at h
    simp only [Pi.zero_apply, mul_zero, zero_sub, Finset.sum_neg_distrib, neg_eq_zero] at h
    simpa [Finset.sum_ite_eq', Function.update_apply] using h
  exact Prod.ext (funext h1) (funext h2)

/--
[bilinForm_basis_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma bilinForm_basis_expand
  [AddCommGroup V]
  [Module ℝ V]
  [Fintype ι]
  {Ω : LinearMap.BilinForm ℝ V}
  {B : Basis ι ℝ V}
  {u v : V} :
-- imply
  Ω u v = ∑ i, ∑ j, (B.repr u i) * (B.repr v j) * Ω (B i) (B j) := by
-- proof
  conv_lhs => rw [← B.sum_repr u]
  rw [LinearMap.BilinForm.sum_left]
  congr 1; ext i
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  conv_lhs => rw [← B.sum_repr v]
  rw [LinearMap.BilinForm.sum_right]
  rw [Finset.mul_sum]
  congr 1; ext j
  rw [map_smul, smul_eq_mul]
  ring

/--
[linear_darboux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma linear_darboux
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  ∃ (n : ℕ) (φ : V ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ)), ∀ u v, Ω u v = stdSymplForm n (φ u) (φ v) := by
-- proof
  obtain ⟨n, e, f, hdim, hee, hff, hef, hli, hspan⟩ := symplectic_standard_basis hΩ
  let B : Basis (Fin n ⊕ Fin n) ℝ V := Basis.mk hli hspan
  let ψ₁ : V ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := B.equivFun
  let ψ₂ : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ) :=
    LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) ℝ ℝ
  let φ : V ≃ₗ[ℝ] (Fin n → ℝ) × (Fin n → ℝ) := ψ₁.trans ψ₂
  refine ⟨n, φ, ?_⟩
  have hB : ∀ i, B i = Sum.elim e f i := fun i => Basis.mk_apply hli hspan i
  have hφ : ∀ v : V, φ v = (fun i => B.repr v (Sum.inl i), fun i => B.repr v (Sum.inr i)) := by
    intro v; rfl
  intro u v
  rw [stdSymplForm_apply, bilinForm_basis_expand Ω B u v]
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, hB, Sum.elim_inl, Sum.elim_inr]
  simp only [hee, hff, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  have hfe : ∀ i j, Ω (f i) (e j) = if i = j then -1 else 0 := by
    intro i j
    rw [sympl_skew hΩ.alt (f i) (e j), hef j i]
    split
    · simp_all
    · simp_all [Ne.symm]
  simp only [hef, hfe]
  rw [hφ u, hφ v]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/--
[IsIsotopic.toIsDeformationEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma IsIsotopic.toIsDeformationEquivalent
  {Ω : ℕ → Type*}
  [DifferentialFormSpace Ω VF]
  [TopologicalSpace (Ω 2)]
  {ω₀ ω₁ : Ω 2}
-- given
  (h : IsIsotopic (VF := VF) ω₀ ω₁) :
-- imply
  IsDeformationEquivalent (VF := VF) ω₀ ω₁ := by
-- proof
  obtain ⟨ω, hcont, hclosed, hnd, h0, h1, _⟩ := h
  exact ⟨ω, hcont, hclosed, hnd, h0, h1⟩

/--
[moser_lie_deriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma moser_lie_deriv_eq
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {t : ℝ}
-- given
  (setup : MoserSetup (Ω := Ω) (VF := VF))
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  inst.L (setup.X_t t) (setup.ω_t t) = -(inst.d (setup.α_t t)) := by
-- proof
  rw [cartan_formula (setup.X_t t) (setup.ω_t t)]
  rw [setup.X_t_eq t ht]
  rw [setup.closed_t t ht, ι_zero_val, add_zero]
  have hd_neg : inst.d (-(setup.α_t t)) = -(inst.d (setup.α_t t)) := by
    have := inst.d_smul (-1 : ℝ) (setup.α_t t)
    simp at this
    exact this
  exact hd_neg

/--
[moser_transport_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma moser_transport_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {t : ℝ}
-- given
  (setup : MoserSetup (Ω := Ω) (VF := VF))
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  inst.L (setup.X_t t) (setup.ω_t t) + setup.dω_dt t = 0 := by
-- proof
  rw [moser_lie_deriv_eq setup t ht, setup.defining_eq t ht]
  exact neg_add_cancel _

/--
[moser_flow_transport_const](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma moser_flow_transport_const
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {flow : MoserFlow setup}
-- given
  (setup : MoserSetup (Ω := Ω) (VF := VF)) :
-- imply
  (∀ t, t ∈ Set.Icc (0 : ℝ) 1 → inst.L (setup.X_t t) (setup.ω_t t) + setup.dω_dt t = 0) → ∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (flow.ρ t).pullback (setup.ω_t t) = setup.ω_t 0 := by
-- proof
  intro htransport
  apply flow.deriv_zero_const
  intro t ht
  rw [flow.flow_ode t ht, htransport t ht]
  have := (flow.ρ t).pullback_smul (0 : ℝ) (0 : Ω 2)
  simp [zero_smul] at this
  exact this

/--
[moser_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma moser_theorem
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {flow : MoserFlow setup}
-- given
  (setup : MoserSetup (Ω := Ω) (VF := VF)) :
-- imply
  (∀ {p : ℕ} (α : Ω p), (flow.ρ 0).pullback α = α) ∧ (∀ t, t ∈ Set.Icc (0 : ℝ) 1 → (flow.ρ t).pullback (setup.ω_t t) = setup.ω_t 0) :=
-- proof
  ⟨flow.ρ_zero, moser_flow_transport_const setup flow (fun t ht => moser_transport_zero setup t ht)⟩

/--
[interpolating_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma interpolating_closed
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {ω₀ ω₁ : Ω 2}
  {t : ℝ}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0) :
-- imply
  inst.d ((1 - t) • ω₀ + t • ω₁) = 0 := by
-- proof
  rw [inst.d_add, inst.d_smul, inst.d_smul, hclosed₀, hclosed₁,
    smul_zero, smul_zero, add_zero]

/--
[contraction_interpolation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma contraction_interpolation
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {ω₀ ω₁ : Ω 2}
  {t : ℝ} :
-- imply
  inst.ι X ((1 - t) • ω₀ + t • ω₁) = (1 - t) • inst.ι X ω₀ + t • inst.ι X ω₁ := by
-- proof
  rw [inst.ι_add, inst.ι_smul, inst.ι_smul]

/--
[contraction_interpolation_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma contraction_interpolation_zero
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {ω₀ ω₁ : Ω 2} :
-- imply
  inst.ι X ((1 - (0 : ℝ)) • ω₀ + (0 : ℝ) • ω₁) = inst.ι X ω₀ := by
-- proof
  rw [contraction_interpolation]
  simp

/--
[contraction_interpolation_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma contraction_interpolation_one
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  {X : VF}
  {ω₀ ω₁ : Ω 2} :
-- imply
  inst.ι X ((1 - (1 : ℝ)) • ω₀ + (1 : ℝ) • ω₁) = inst.ι X ω₁ := by
-- proof
  rw [contraction_interpolation]
  simp

/--
[interpolated_form_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma interpolated_form_nondegenerate
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hfdc : HasFiniteDimContraction Ω VF]
  {ω₀ ω₁ : Ω 2}
  {t : ℝ}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
  (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  Function.Injective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁)) :=
-- proof
  hfdc.interpolated_contraction_injective ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht

/--
[interpolated_form_contraction_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma interpolated_form_contraction_surjective
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hfdc : HasFiniteDimContraction Ω VF]
  {ω₀ ω₁ : Ω 2}
  {t : ℝ}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
  (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  Function.Surjective (fun (X : VF) => inst.ι X ((1 - t) • ω₀ + t • ω₁)) :=
-- proof
  hfdc.contraction_surjective_of_injective _
    (interpolated_form_nondegenerate (hfdc := hfdc) ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht)

/--
[local_moser_interior_product_solvable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma local_moser_interior_product_solvable
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hfdc : HasFiniteDimContraction Ω VF]
  {ω₀ ω₁ : Ω 2}
  {α : Ω 1}
  {t : ℝ}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
  (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
  (_hα : inst.d α = ω₁ - ω₀)
  (ht : t ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  ∃ (X : VF), inst.ι X ((1 - t) • ω₀ + t • ω₁) = -α :=
-- proof
interpolated_form_contraction_surjective ω₀ ω₁ hclosed₀ hclosed₁ hnd₀ hnd₁ t ht (-α)

/--
[local_moser_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean)
-/
@[path]
lemma local_moser_theorem
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hfdc : HasFiniteDimContraction Ω VF]
  {ω₀ ω₁ : Ω 2}
-- given
  (hclosed₀ : inst.d ω₀ = 0)
  (hclosed₁ : inst.d ω₁ = 0)
  (hnd₀ : Function.Injective (fun X => inst.ι X ω₀))
  (hnd₁ : Function.Injective (fun X => inst.ι X ω₁))
  (hcohom : ∃ α : Ω 1, inst.d α = ω₁ - ω₀)
  (hflow_exists : ∀ (s : MoserSetup (Ω := Ω) (VF := VF)), MoserFlow s) :
-- imply
  ∃ (φ : DFSMorphism Ω VF Ω VF), φ.pullback ω₁ = ω₀ := by
-- proof
  obtain ⟨α, hα⟩ := hcohom
  have hsolve : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    ∃ (X : VF), inst.ι X ((1 - t) • ω₀ + t • ω₁) = -α :=
    fun t ht => local_moser_interior_product_solvable ω₀ ω₁ α hclosed₀ hclosed₁ hnd₀ hnd₁ hα t ht
  have hinst : Nonempty VF := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
    exact ⟨(hsolve 0 h0).choose⟩
  let X_t : ℝ → VF := fun t =>
    if h : t ∈ Set.Icc (0 : ℝ) 1 then (hsolve t h).choose else Classical.arbitrary VF
  have hX_t : ∀ t, t ∈ Set.Icc (0 : ℝ) 1 →
    inst.ι (X_t t) ((1 - t) • ω₀ + t • ω₁) = -α := by
    intro t ht
    simp only [X_t, dif_pos ht]
    exact (hsolve t ht).choose_spec
  let setup : MoserSetup (Ω := Ω) (VF := VF) :=
    { ω_t := fun t => (1 - t) • ω₀ + t • ω₁
      closed_t := fun t _ => interpolating_closed ω₀ ω₁ hclosed₀ hclosed₁ t
      α_t := fun _ => α
      dω_dt := fun _ => ω₁ - ω₀
      derivative_consistency := by
        intro t s _ _
        simp [smul_sub, sub_smul]
        abel
      defining_eq := fun _ _ => hα
      X_t := X_t
      X_t_eq := hX_t }
  let flow : MoserFlow setup := hflow_exists setup
  have hmoser := moser_theorem setup flow
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have htransport := hmoser.2 1 h1_mem
  have hω1 : setup.ω_t 1 = ω₁ := by simp [setup]
  have hω0 : setup.ω_t 0 = ω₀ := by simp [setup]
  rw [hω1, hω0] at htransport
  exact ⟨flow.ρ 1, htransport⟩


-- created on 2026-10-23
