import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalStructuresGraded


/--
[monoidalNatTransData_mul_character](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma monoidalNatTransData_mul_character
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A}
  {η : Cochain1 G A}
  {χ : G →* A}
-- given
  (hη : IsMonoidalNatTransData G A μ μ' η) :
-- imply
  IsMonoidalNatTransData G A μ μ' (fun g => χ g * η g) := by
-- proof
  intro g h
  have hχ : χ (g * h) = χ g * χ h := map_mul χ g h
  have := hη g h
  calc χ g * η g * (χ h * η h) * μ g h
    = χ g * χ h * (η g * η h * μ g h) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = χ g * χ h * (μ' g h * η (g * h)) := by rw [this]
    _ = μ' g h * (χ g * χ h * η (g * h)) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    _ = μ' g h * (χ (g * h) * η (g * h)) := by rw [hχ]

/--
[monoidalNatTrans_ratio_is_character](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma monoidalNatTrans_ratio_is_character
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A}
  {η η' : Cochain1 G A}
-- given
  (hη : IsMonoidalNatTransData G A μ μ' η)
  (hη' : IsMonoidalNatTransData G A μ μ' η') :
-- imply
  ∃ χ : G →* A, ∀ g : G, η' g = χ g * η g := by
-- proof
  have hd : ∀ g h : G, d1 G A η g h = d1 G A η' g h := by
    intro g h
    have h1 := (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mp hη g h
    have h2 := (isMonoidalNatTransData_iff_coboundary G A μ μ' η').mp hη' g h
    rw [h1] at h2
    exact mul_left_cancel h2
  refine ⟨{
    toFun := fun g => η' g * (η g)⁻¹
    map_one' := ?_
    map_mul' := ?_
  }, fun g => ?_⟩
  · have h1 := hd 1 1
    unfold d1 at h1
    simp [mul_one] at h1
    simp [h1]
  · intro g h
    have key := hd g h
    unfold d1 at key
    have step : η g * η h * η' (g * h) = η' g * η' h * η (g * h) := by
      calc η g * η h * η' (g * h)
        = η g * η h * (η (g * h))⁻¹ * η (g * h) * η' (g * h) := by
          simp [mul_assoc, mul_inv_cancel]
        _ = η' g * η' h * (η' (g * h))⁻¹ * η (g * h) * η' (g * h) := by
          rw [key]
        _ = η' g * η' h * η (g * h) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
    have factor : η' (g * h) = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) := by
      calc η' (g * h)
        = (η g * η h)⁻¹ * (η g * η h * η' (g * h)) := by
          simp [mul_assoc, inv_mul_cancel]
        _ = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) := by rw [step]
    calc η' (g * h) * (η (g * h))⁻¹
      = (η g * η h)⁻¹ * (η' g * η' h * η (g * h)) * (η (g * h))⁻¹ := by
        rw [factor]
      _ = (η g * η h)⁻¹ * (η' g * η' h) := by
        simp [mul_assoc, mul_inv_cancel]
      _ = (η' g * (η g)⁻¹) * (η' h * (η h)⁻¹) := by
        simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  · simp [mul_comm]

/--
[Proposition_1_7_1_i_torsor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma Proposition_1_7_1_i_torsor
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {G₁ : Type u}
  [Group G₁]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G₁ A} :
-- imply
  ((∃ η : Cochain1 G₁ A, IsMonoidalNatTransData G₁ A μ μ' η) ↔ Cohomologous2 G₁ A μ μ') ∧ (∀ {η η' : Cochain1 G₁ A}, IsMonoidalNatTransData G₁ A μ μ' η → IsMonoidalNatTransData G₁ A μ μ' η' → ∃ χ : G₁ →* A, ∀ g : G₁, η' g = χ g * η g) ∧ (∀ {η : Cochain1 G₁ A}, IsMonoidalNatTransData G₁ A μ μ' η → ∀ χ : G₁ →* A, IsMonoidalNatTransData G₁ A μ μ' (fun g => χ g * η g)) :=
-- proof
  ⟨monoidalNatTrans_iff_cohomologous2 G₁ A μ μ',
    fun hη hη' => monoidalNatTrans_ratio_is_character hη hη',
    fun hη χ => monoidalNatTransData_mul_character hη χ⟩
section PartII
variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/--
[Proposition_1_7_1_ii_torsor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma Proposition_1_7_1_ii_torsor
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A} :
-- imply
  ((∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔ Cohomologous2 G A μ μ') ∧ ((∃ η : Cochain1 G A, ∀ g h : G, μ' g h = μ g h * d1 G A η g h) ↔ @Quotient.mk _ (cohomologous2Setoid G A) μ = @Quotient.mk _ (cohomologous2Setoid G A) μ') :=
-- proof
  ⟨monoidal_iso_iff_cohomologous2 G A μ μ',
    monoidal_autoequiv_classes_H2 G A μ μ'⟩
end PartII
section PartIII
variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/--
[autPullback3_eq_pullback3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma autPullback3_eq_pullback3
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {φ : G ≃* G}
  {ω : Cochain3' G A} :
-- imply
  autPullback3 G A φ ω = pullback3 G G A φ.toMonoidHom ω := by
-- proof
  rfl

/--
[monoidal_equiv_general_iff_autOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma monoidal_equiv_general_iff_autOrbit
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω₁ ω₂ : Cochain3' G A} :
-- imply
  (∃ (φ : G ≃* G) (μ : Cochain2 G A), IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔ AutOrbitCohomologous3 G A ω₁ ω₂ := by
-- proof
  unfold AutOrbitCohomologous3
  simp_rw [autPullback3_eq_pullback3]
  constructor
  · rintro ⟨φ, μ, hμ⟩
    exact ⟨φ, (monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ φ.toMonoidHom).mp ⟨μ, hμ⟩⟩
  · rintro ⟨φ, hcohom⟩
    obtain ⟨μ, hμ⟩ := (monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ φ.toMonoidHom).mpr hcohom
    exact ⟨φ, μ, hμ⟩

/--
[Proposition_1_7_1_iii_with_OutG](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma Proposition_1_7_1_iii_with_OutG
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω₁ ω₂ : Cochain3' G A} :
-- imply
  ((∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔ Cohomologous3 G A ω₁ ω₂) ∧ ((∃ (φ : G ≃* G) (μ : Cochain2 G A), IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔ AutOrbitCohomologous3 G A ω₁ ω₂) :=
-- proof
  ⟨monoidal_equiv_iff_cohomologous3 G A ω₁ ω₂,
    monoidal_equiv_general_iff_autOrbit G A ω₁ ω₂⟩
end PartIII

/--
[Proposition_1_7_1_combined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalStructuresGraded.lean)
-/
@[path]
lemma Proposition_1_7_1_combined
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A] :
-- imply
  (∀ μ μ' : Cochain2 G A, ((∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔ Cohomologous2 G A μ μ') ∧ (∀ {η η' : Cochain1 G A}, IsMonoidalNatTransData G A μ μ' η → IsMonoidalNatTransData G A μ μ' η' → ∃ χ : G →* A, ∀ g : G, η' g = χ g * η g) ∧ (∀ {η : Cochain1 G A}, IsMonoidalNatTransData G A μ μ' η → ∀ χ : G →* A, IsMonoidalNatTransData G A μ μ' (fun g => χ g * η g))) ∧ (∀ μ μ' : Cochain2 G A, ((∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔ Cohomologous2 G A μ μ') ∧ ((∃ η : Cochain1 G A, ∀ g h : G, μ' g h = μ g h * d1 G A η g h) ↔ @Quotient.mk _ (cohomologous2Setoid G A) μ = @Quotient.mk _ (cohomologous2Setoid G A) μ')) ∧ (∀ ω₁ ω₂ : Cochain3' G A, ((∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔ Cohomologous3 G A ω₁ ω₂) ∧ ((∃ (φ : G ≃* G) (μ : Cochain2 G A), IsMonoidalFunctorData G G A ω₁ ω₂ φ.toMonoidHom μ) ↔ AutOrbitCohomologous3 G A ω₁ ω₂)) :=
-- proof
  ⟨fun μ μ' => Proposition_1_7_1_i_torsor μ μ',
    fun μ μ' => Proposition_1_7_1_ii_torsor G A μ μ',
    fun ω₁ ω₂ => Proposition_1_7_1_iii_with_OutG G A ω₁ ω₂⟩


-- created on 2026-10-23
