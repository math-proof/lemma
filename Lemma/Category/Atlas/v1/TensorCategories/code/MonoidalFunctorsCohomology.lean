import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
open CategoryTheory


/--
[prod4_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma prod4_eq_one_iff
  [CommGroup A]
  {a b c d : A} :
-- imply
  a * b * c⁻¹ * d⁻¹ = 1 ↔ d * c = a * b := by
-- proof
  rw [eq_comm (a := d * c)]
  show a * b * c⁻¹ * d⁻¹ = 1 ↔ a * b = d * c
  rw [show (a * b * c⁻¹ * d⁻¹ : A) = a * b / (d * c) from by
    simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]]
  exact div_eq_one

/--
[comm_group_rearrange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma comm_group_rearrange
  [CommGroup A]
  {x a b c d : A} :
-- imply
  x * (a * b * c⁻¹ * d⁻¹) * d * c = x * a * b := by
-- proof
  simp [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel]
section CoboundarySquare
variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/--
[d2_comp_d1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma d2_comp_d1
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {η : Cochain1 G A}
-- given
  (g h l : G) :
-- imply
  d2 G A (d1 G A η) g h l = 1 := by
-- proof
  unfold d2 d1
  rw [show g * (h * l) = g * h * l from (mul_assoc g h l).symm]
  set a := η g; set b := η h; set c := η l
  set d := η (h * l); set e := η (g * h * l); set f := η (g * h)
  simp only [mul_inv_rev, inv_inv]
  calc b * c * d⁻¹ * (a * d * e⁻¹) * (e * (c⁻¹ * f⁻¹)) * (f * (b⁻¹ * a⁻¹))
    = (a * a⁻¹) * (b * b⁻¹) * (c * c⁻¹) * (d * d⁻¹) * (e * e⁻¹) * (f * f⁻¹) := by
      simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = 1 := by simp [mul_inv_cancel]

/--
[isCocycle2_iff_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma isCocycle2_iff_assoc
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ : Cochain2 G A} :
-- imply
  IsCocycle2 G A μ ↔ ∀ g h l : G, μ g h * μ (g * h) l = μ h l * μ g (h * l) := by
-- proof
  unfold IsCocycle2 d2
  constructor
  · intro hμ g h l
    have := hμ g h l
    rwa [prod4_eq_one_iff] at this
  · intro hμ g h l
    rw [prod4_eq_one_iff]
    exact hμ g h l

/--
[isMonoidalFunctorData_iff_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma isMonoidalFunctorData_iff_pullback
  {G₁ : Type u}
  [Group G₁]
  {G₂ : Type u}
  [Group G₂]
  {A : Type v}
  [CommGroup A]
  {ω₁ : Cochain3' G₁ A}
  {ω₂ : Cochain3' G₂ A}
  {f : G₁ →* G₂}
  {μ : Cochain2 G₁ A} :
-- imply
  IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ ↔ ∀ g h l : G₁, pullback3 G₁ G₂ A f ω₂ g h l = ω₁ g h l * d2 G₁ A μ g h l := by
-- proof
  unfold IsMonoidalFunctorData pullback3 d2
  constructor
  ·
    intro hnat g h l
    have := hnat g h l
    calc ω₂ (f g) (f h) (f l)
      = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l * (μ (g * h) l)⁻¹ * (μ g h)⁻¹ := by
        simp [mul_assoc, mul_inv_cancel]
      _ = ω₁ g h l * μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹ := by rw [← this]
      _ = ω₁ g h l * (μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
  ·
    intro hpb g h l
    have := hpb g h l
    calc ω₁ g h l * μ h l * μ g (h * l)
      = ω₁ g h l * (μ h l * μ g (h * l) * (μ (g * h) l)⁻¹ * (μ g h)⁻¹) * μ g h * μ (g * h) l :=
        comm_group_rearrange.symm
      _ = ω₂ (f g) (f h) (f l) * μ g h * μ (g * h) l := by rw [← this]

/--
[monoidalFunctor_exists_iff_cohomologous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidalFunctor_exists_iff_cohomologous
  {G₁ : Type u}
  [Group G₁]
  {G₂ : Type u}
  [Group G₂]
  {A : Type v}
  [CommGroup A]
  {ω₁ : Cochain3' G₁ A}
  {ω₂ : Cochain3' G₂ A}
  {f : G₁ →* G₂} :
-- imply
  (∃ μ : Cochain2 G₁ A, IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f μ) ↔ Cohomologous3 G₁ A ω₁ (pullback3 G₁ G₂ A f ω₂) := by
-- proof
  constructor
  ·
    rintro ⟨μ, hμ⟩
    exact ⟨μ, fun g h l =>
      ((isMonoidalFunctorData_iff_pullback G₁ G₂ A ω₁ ω₂ f μ).mp hμ) g h l⟩
  ·
    rintro ⟨μ, hμ⟩
    exact ⟨μ, (isMonoidalFunctorData_iff_pullback G₁ G₂ A ω₁ ω₂ f μ).mpr hμ⟩
section MonoidalNatTrans
variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/--
[isMonoidalNatTransData_iff_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma isMonoidalNatTransData_iff_coboundary
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A}
  {η : Cochain1 G A} :
-- imply
  IsMonoidalNatTransData G A μ μ' η ↔ ∀ g h : G, μ' g h = μ g h * d1 G A η g h := by
-- proof
  unfold IsMonoidalNatTransData d1
  constructor
  · intro H g h
    have key : μ' g h * η (g * h) = μ g h * η g * η h := by
      rw [← H g h]; simp [mul_comm, mul_left_comm]
    calc μ' g h = μ' g h * η (g * h) * (η (g * h))⁻¹ := by
      simp
      _ = μ g h * η g * η h * (η (g * h))⁻¹ := by rw [key]
      _ = μ g h * (η g * η h * (η (g * h))⁻¹) := by
        simp [mul_assoc]
  · intro H g h
    rw [H g h]
    simp [mul_assoc, mul_comm, mul_left_comm]

/--
[monoidalNatTrans_iff_cohomologous2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidalNatTrans_iff_cohomologous2
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A} :
-- imply
  (∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔ Cohomologous2 G A μ μ' := by
-- proof
  unfold Cohomologous2
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨η, (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mp hη⟩
  · rintro ⟨η, hη⟩
    exact ⟨η, (isMonoidalNatTransData_iff_coboundary G A μ μ' η).mpr hη⟩
end MonoidalNatTrans
section Classification
variable (G : Type u) [Group G] (A : Type v) [CommGroup A]

/--
[isMonoidalNatIso_of_isMonoidalNatTransData](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma isMonoidalNatIso_of_isMonoidalNatTransData
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A}
  {η : Cochain1 G A}
-- given
  (h : IsMonoidalNatTransData G A μ μ' η) :
-- imply
  IsMonoidalNatIso G A μ μ' η :=
-- proof
  ⟨h, fun _ => (η _)⁻¹, fun _ => ⟨mul_inv_cancel _, inv_mul_cancel _⟩⟩

/--
[monoidal_iso_iff_cohomologous2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidal_iso_iff_cohomologous2
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A} :
-- imply
  (∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔ Cohomologous2 G A μ μ' := by
-- proof
  constructor
  ·
    rintro ⟨η, h_trans, _⟩
    exact (monoidalNatTrans_iff_cohomologous2 G A μ μ').mp ⟨η, h_trans⟩
  ·
    intro h_cohom
    obtain ⟨η, hη⟩ := (monoidalNatTrans_iff_cohomologous2 G A μ μ').mpr h_cohom
    exact ⟨η, isMonoidalNatIso_of_isMonoidalNatTransData G A μ μ' η hη⟩

/--
[monoidal_autoequiv_classes_H2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidal_autoequiv_classes_H2
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ₁ μ₂ : Cochain2 G A} :
-- imply
  (∃ η : Cochain1 G A, ∀ g h : G, μ₂ g h = μ₁ g h * d1 G A η g h) ↔ @Quotient.mk _ (cohomologous2Setoid G A) μ₁ = @Quotient.mk _ (cohomologous2Setoid G A) μ₂ := by
-- proof
  constructor
  · intro ⟨η, hη⟩
    apply Quotient.sound
    exact ⟨η, hη⟩
  · intro h
    exact Quotient.exact h

/--
[pullback3_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma pullback3_id
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : Cochain3' G A} :
-- imply
  pullback3 G G A (MonoidHom.id G) ω = ω := by
-- proof
  funext g h l
  simp [pullback3]

/--
[monoidal_equiv_iff_cohomologous3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidal_equiv_iff_cohomologous3
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω₁ ω₂ : Cochain3' G A} :
-- imply
  (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔ Cohomologous3 G A ω₁ ω₂ := by
-- proof
  rw [monoidalFunctor_exists_iff_cohomologous G G A ω₁ ω₂ (MonoidHom.id G),
    pullback3_id G A ω₂]

/--
[monoidal_structure_parametrized_by_H3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma monoidal_structure_parametrized_by_H3
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω₁ ω₂ : Cochain3' G A} :
-- imply
  (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔ @Quotient.mk _ (cohomologous3Setoid G A) ω₁ = @Quotient.mk _ (cohomologous3Setoid G A) ω₂ := by
-- proof
  rw [monoidal_equiv_iff_cohomologous3 G A ω₁ ω₂]
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h
end Classification
section GradedVecConnection
variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

/--
[Proposition_1_7_1_i](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma Proposition_1_7_1_i
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A} :
-- imply
  (∃ η : Cochain1 G A, IsMonoidalNatTransData G A μ μ' η) ↔ Cohomologous2 G A μ μ' :=
-- proof
  monoidalNatTrans_iff_cohomologous2 G A μ μ'

/--
[Proposition_1_7_1_ii](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma Proposition_1_7_1_ii
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ μ' : Cochain2 G A} :
-- imply
  (∃ η : Cochain1 G A, IsMonoidalNatIso G A μ μ' η) ↔ Cohomologous2 G A μ μ' :=
-- proof
  monoidal_iso_iff_cohomologous2 G A μ μ'

/--
[Proposition_1_7_1_iii](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
lemma Proposition_1_7_1_iii
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω₁ ω₂ : Cochain3' G A} :
-- imply
  (∃ μ : Cochain2 G A, IsMonoidalFunctorData G G A ω₁ ω₂ (MonoidHom.id G) μ) ↔ @Quotient.mk _ (cohomologous3Setoid G A) ω₁ = @Quotient.mk _ (cohomologous3Setoid G A) ω₂ :=
-- proof
  monoidal_structure_parametrized_by_H3 G A ω₁ ω₂

/--
[prod5_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma prod5_eq_one_iff_eq
  [CommGroup A]
  {a b c d e : A} :
-- imply
  a * b * c * d⁻¹ * e⁻¹ = 1 ↔ e * d = a * b * c := by
-- proof
  apply prod5_eq_one_iff

/--
[d1_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma d1_inv_eq
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {η : Cochain1 G A}
-- given
  (g h : G) :
-- imply
  d1 G A (fun x => (η x)⁻¹) g h = (d1 G A η g h)⁻¹ := by
-- proof
  apply d1_inv G A η g h

/--
[d2_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma d2_inv_eq
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {μ : Cochain2 G A}
-- given
  (g h l : G) :
-- imply
  d2 G A (fun x y => (μ x y)⁻¹) g h l = (d2 G A μ g h l)⁻¹ := by
-- proof
  apply d2_inv G A μ g h l

/--
[isCocycle3_iff_cocycleCond](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma isCocycle3_iff_cocycleCond_eq
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : Cochain3' G A} :
-- imply
  IsCocycle3 G A ω ↔ ∀ g₁ g₂ g₃ g₄ : G, ω (g₁ * g₂) g₃ g₄ * ω g₁ g₂ (g₃ * g₄) = ω g₁ g₂ g₃ * ω g₁ (g₂ * g₃) g₄ * ω g₂ g₃ g₄ := by
-- proof
  apply isCocycle3_iff_cocycleCond G A ω

/--
[isMonoidalFunctorData_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma isMonoidalFunctorData_id_eq
  {G : Type u}
  [Group G]
  {A : Type v}
  [CommGroup A]
  {ω : Cochain3' G A} :
-- imply
  IsMonoidalFunctorData G G A ω ω (MonoidHom.id G) (fun _ _ => 1) := by
-- proof
  apply isMonoidalFunctorData_id G A ω

/--
[isMonoidalFunctorData_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorsCohomology.lean)
-/
@[path]
private lemma isMonoidalFunctorData_comp_eq
  {G₁ G₂ G₃ : Type u}
  [Group G₁]
  [Group G₂]
  [Group G₃]
  {A : Type v}
  [CommGroup A]
  {ω₁ : Cochain3' G₁ A}
  {ω₂ : Cochain3' G₂ A}
  {ω₃ : Cochain3' G₃ A}
  {f₁ : G₁ →* G₂}
  {f₂ : G₂ →* G₃}
  {μ₁ : Cochain2 G₁ A}
  {μ₂ : Cochain2 G₂ A}
-- given
  (h₁ : IsMonoidalFunctorData G₁ G₂ A ω₁ ω₂ f₁ μ₁)
  (h₂ : IsMonoidalFunctorData G₂ G₃ A ω₂ ω₃ f₂ μ₂) :
-- imply
  IsMonoidalFunctorData G₁ G₃ A ω₁ ω₃ (f₂.comp f₁) (compCochain2 f₁ μ₁ μ₂) := by
-- proof
  apply isMonoidalFunctorData_comp h₁ h₂


-- created on 2026-10-23
