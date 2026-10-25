import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Thm1023
open Ideal Polynomial
open scoped Pointwise


/--
[hensel_lift_ramificationIdx_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma hensel_lift_ramificationIdx_eq_one
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {α : IsLocalRing.ResidueField B}
  {β : B}
  [IsDiscreteValuationRing ↥(integralClosure A ↥(IntermediateField.adjoin K {algebraMap B L β}))]
  [IsLocalHom (algebraMap A ↥(integralClosure A ↥(IntermediateField.adjoin K {algebraMap B L β})))]
-- given
  (hα : IntermediateField.adjoin (IsLocalRing.ResidueField A) {α} = ⊤)
  (hβ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) β = α) :
-- imply
  (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal ↥(integralClosure A ↥(IntermediateField.adjoin K {algebraMap B L β}))) = 1 := by
-- proof
  set E₀ := IntermediateField.adjoin K {algebraMap B L β}
  set C := integralClosure A ↥E₀
  haveI : FiniteDimensional K ↥E₀ := IntermediateField.finiteDimensional_left E₀
  haveI : Algebra.IsSeparable K ↥E₀ := IntermediateField.isSeparable_tower_bot K E₀
  haveI hFU : Algebra.FormallyUnramified A ↥C :=
    formallyUnramified_integralClosure_of_complete_dvr A K ↥E₀
  haveI : IsFractionRing ↥C ↥E₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥E₀
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥E₀ (integralClosure A ↥E₀)
  haveI : Module.Finite A ↥C := inferInstance
  haveI : Algebra.EssFiniteType A ↥C :=
    Algebra.EssFiniteType.of_finiteType A ↥C
  letI algCL : Algebra ↥C L :=
    ((E₀.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E₀.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective φ
    intro x y hxy
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
  have hmap_eq : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥C :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmap_ne_top : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap_eq]; exact (IsLocalRing.maximalIdeal.isMaximal ↥C).ne_top
  have hmap_ne_bot : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [hmap_eq]; exact IsDiscreteValuationRing.not_a_field ↥C
  have hram := Ideal.ramificationIdx_map_self_eq_one hmap_ne_top hmap_ne_bot
  rwa [hmap_eq] at hram

/--
[integralClosure_formallyUnramified_of_hensel_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma integralClosure_formallyUnramified_of_hensel_lift
  {α : IsLocalRing.ResidueField B}
  {β : B}
-- given
  (hα : IntermediateField.adjoin (IsLocalRing.ResidueField A) {α} = ⊤)
  (hβ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) β = α) :
-- imply
  Algebra.FormallyUnramified A (integralClosure A ↥(IntermediateField.adjoin K {algebraMap B L β})) := by
-- proof
  set E₀ := IntermediateField.adjoin K {algebraMap B L β}
  set C := integralClosure A ↥E₀
  haveI : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L E₀
  letI algCL : Algebra ↥C L := ((E₀.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom ((E₀.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective φ
    intro x y hxy
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  haveI hlocal_A_C : IsLocalHom (algebraMap A ↥C) := by
    have : IsLocalHom ((algebraMap ↥C B).comp (algebraMap A ↥C)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C B]
    exact isLocalHom_of_comp _ (algebraMap ↥C B)
  haveI : FiniteDimensional K ↥E₀ := IntermediateField.finiteDimensional_left E₀
  haveI : IsFractionRing ↥C ↥E₀ := integralClosure.isFractionRing_of_finite_extension K ↥E₀
  haveI : IsNoetherian A ↥C := IsIntegralClosure.isNoetherian A K ↥E₀ (integralClosure A ↥E₀)
  haveI : Module.Finite A ↥C := inferInstance
  haveI : Algebra.EssFiniteType A ↥C := Algebra.EssFiniteType.of_finiteType A ↥C
  haveI : FaithfulSMul ↥C B := (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI hlocal_C_B : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
  have hmap : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥C := by
    exact map_maximalIdeal_eq_of_ramificationIdx_one A ↥C
      (hensel_lift_ramificationIdx_eq_one α hα β hβ)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

/--
[adjoin_degree_eq_resDeg_of_hensel_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma adjoin_degree_eq_resDeg_of_hensel_lift
  {α : IsLocalRing.ResidueField B}
  {β : B}
-- given
  (hα : IntermediateField.adjoin (IsLocalRing.ResidueField A) {α} = ⊤)
  (hβ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) β = α) :
-- imply
  Module.finrank K ↥(IntermediateField.adjoin K {algebraMap B L β}) = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
-- proof
  set E₀ := IntermediateField.adjoin K ({algebraMap B L β} : Set L)
  set C := integralClosure A ↥E₀
  haveI : FiniteDimensional K ↥E₀ := IntermediateField.finiteDimensional_left E₀
  haveI : Algebra.IsSeparable K ↥E₀ := IntermediateField.isSeparable_tower_bot K E₀
  haveI hFU : Algebra.FormallyUnramified A ↥C :=
    integralClosure_formallyUnramified_of_hensel_lift A K B L α hα β hβ
  haveI hDVR : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L E₀
  haveI : IsFractionRing ↥C ↥E₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥E₀
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥E₀ C
  haveI : Module.Finite A ↥C := inferInstance
  letI algCL : Algebra ↥C L :=
    ((E₀.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E₀.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective φ
    intro x y hxy
    have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI hLH_CB : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI hLC : IsLocalHom (algebraMap A ↥C) := by
    have : IsLocalHom ((algebraMap ↥C B).comp (algebraMap A ↥C)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C B]
    exact isLocalHom_of_comp _ (algebraMap ↥C B)
  haveI : Algebra.EssFiniteType A ↥C :=
    Algebra.EssFiniteType.of_finiteType A ↥C
  haveI : (IsLocalRing.maximalIdeal ↥C).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    ↥C K ↥E₀ (IsDiscreteValuationRing.not_a_field A)
  have hmap_eq : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥C :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hmap_eq] at hfund
  have hmap_ne_top : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap_eq]; exact (IsLocalRing.maximalIdeal.isMaximal ↥C).ne_top
  have hmap_ne_bot : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [hmap_eq]; exact IsDiscreteValuationRing.not_a_field ↥C
  rw [Ideal.ramificationIdx_map_self_eq_one hmap_ne_top hmap_ne_bot, one_mul] at hfund
  rw [hmap_eq] at hfund
  rw [Ideal.inertiaDeg_algebraMap] at hfund
  have htower := Ideal.inertiaDeg_algebra_tower
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal ↥C) (IsLocalRing.maximalIdeal B)
  rw [Ideal.inertiaDeg_algebraMap,
    Ideal.inertiaDeg_algebraMap (R := ↥C) (S := B),
    Ideal.inertiaDeg_algebraMap (R := A) (S := ↥C)] at htower
  change Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) =
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) *
      Module.finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) at htower
  change Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) =
    Module.finrank K ↥E₀ at hfund
  have hfCB_eq_one :
    Module.finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = 1 := by
    have hβL_mem : algebraMap B L β ∈ E₀ :=
      IntermediateField.subset_adjoin K {algebraMap B L β} rfl
    have hβE₀_int : (⟨algebraMap B L β, hβL_mem⟩ : ↥E₀) ∈ C := by
      show IsIntegral A (⟨algebraMap B L β, hβL_mem⟩ : ↥E₀)
      rw [← isIntegral_algHom_iff (E₀.val.restrictScalars A) Subtype.val_injective]
      exact (Algebra.IsIntegral.isIntegral (R := A) β).map (IsScalarTower.toAlgHom A B L)
    let β_C : ↥C := ⟨⟨algebraMap B L β, hβL_mem⟩, hβE₀_int⟩
    have hφ_βC : φ β_C = β := by
      apply (IsFractionRing.injective B L)
      exact IsIntegralClosure.algebraMap_lift A B L β_C
    have hα_in_range : α ∈ (algebraMap (IsLocalRing.ResidueField ↥C)
      (IsLocalRing.ResidueField B)).range := by
      rw [RingHom.mem_range]
      exact ⟨Ideal.Quotient.mk _ β_C, by rw [← hβ, ← hφ_βC]; rfl⟩
    have hsurj : Function.Surjective (algebraMap (IsLocalRing.ResidueField ↥C)
      (IsLocalRing.ResidueField B)) := by
      intro y
      have hy : y ∈ IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({α} : Set (IsLocalRing.ResidueField B)) := hα ▸ IntermediateField.mem_top
      refine IntermediateField.adjoin_induction (IsLocalRing.ResidueField A)
        ?_ ?_ ?_ ?_ ?_ hy
      · intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hα_in_range
      · intro a; exact ⟨algebraMap _ _ a, by
        rw [← IsScalarTower.algebraMap_apply (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)]⟩
      · rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add _ _ _⟩
      · rintro _ _ ⟨a, rfl⟩; exact ⟨a⁻¹, map_inv₀ _ _⟩
      · rintro _ _ _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul _ _ _⟩
    have hbij : Function.Bijective (algebraMap (IsLocalRing.ResidueField ↥C)
      (IsLocalRing.ResidueField B)) :=
      ⟨RingHom.injective _, hsurj⟩
    rw [show (1 : ℕ) = Module.finrank (IsLocalRing.ResidueField ↥C)
      (IsLocalRing.ResidueField ↥C) from (Module.finrank_self _).symm]
    exact ((AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq).symm
  rwa [htower, hfCB_eq_one, mul_one]

/--
[thm_10_13_exists_unram_subext_of_degree_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_exists_unram_subext_of_degree_f
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  ∃ (E₀ : IntermediateField K L), IsFiniteUnramifiedSubext A K L E₀ ∧ Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
-- proof
  obtain ⟨α, hα⟩ := Field.exists_primitive_element
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective α
  let β_L : L := algebraMap B L β
  let E₀ : IntermediateField K L := IntermediateField.adjoin K {β_L}
  refine ⟨E₀, ⟨?_, ?_⟩, ?_⟩
  ·
    exact IntermediateField.finiteDimensional_left E₀
  ·
    exact integralClosure_formallyUnramified_of_hensel_lift A K B L α hα β hβ
  ·
    exact adjoin_degree_eq_resDeg_of_hensel_lift A K B L α hα β hβ
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

/--
[thm_10_13_unram_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_unram_le
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E E₀ : IntermediateField K L}
-- given
  (hE : IsFiniteUnramifiedSubext A K L E)
  (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
  (hE₀_deg : Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  E ≤ E₀ := by
-- proof
  obtain ⟨hE_fin, hE_unram⟩ := hE
  obtain ⟨hE₀_fin, hE₀_unram⟩ := hE₀_unram
  haveI : FiniteDimensional K ↥E := hE_fin
  haveI : FiniteDimensional K ↥E₀ := hE₀_fin
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  haveI : Algebra.IsSeparable K ↥E₀ := IntermediateField.isSeparable_tower_bot K E₀
  set C_E := integralClosure A ↥E
  set C_E₀ := integralClosure A ↥E₀
  haveI : Algebra.FormallyUnramified A ↥C_E := hE_unram
  haveI : Algebra.FormallyUnramified A ↥C_E₀ := hE₀_unram
  haveI hDVR_E : IsDiscreteValuationRing ↥C_E := AKLB_intClE_isDVR A K L E
  haveI hDVR_E₀ : IsDiscreteValuationRing ↥C_E₀ := AKLB_intClE_isDVR A K L E₀
  let ι_E_L : ↥C_E →ₐ[A] L := (E.val.restrictScalars A).comp C_E.val
  let ι_E₀_L : ↥C_E₀ →ₐ[A] L := (E₀.val.restrictScalars A).comp C_E₀.val
  letI algCEL : Algebra ↥C_E L := ι_E_L.toAlgebra
  letI algCE₀L : Algebra ↥C_E₀ L := ι_E₀_L.toAlgebra
  haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom ι_E_L
  haveI : IsScalarTower A ↥C_E₀ L := IsScalarTower.of_algHom ι_E₀_L
  haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
  haveI : Algebra.IsIntegral A ↥C_E₀ := integralClosure.AlgebraIsIntegral
  let ι_E : ↥C_E →ₐ[A] B := IsIntegralClosure.lift A B L
  let ι_E₀ : ↥C_E₀ →ₐ[A] B := IsIntegralClosure.lift A B L
  letI algCEB : Algebra ↥C_E B := ι_E.toAlgebra
  letI algCE₀B : Algebra ↥C_E₀ B := ι_E₀.toAlgebra
  haveI : IsScalarTower A ↥C_E B := IsScalarTower.of_algHom ι_E
  haveI : IsScalarTower A ↥C_E₀ B := IsScalarTower.of_algHom ι_E₀
  have hinj_CE_B : Function.Injective (algebraMap ↥C_E B) := by
    change Function.Injective ι_E
    intro x y hxy
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  have hinj_CE₀_B : Function.Injective (algebraMap ↥C_E₀ B) := by
    change Function.Injective ι_E₀
    intro x y hxy
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  haveI : IsLocalHom (algebraMap A ↥C_E) := by
    have : IsLocalHom ((algebraMap ↥C_E B).comp (algebraMap A ↥C_E)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C_E B]
    exact isLocalHom_of_comp _ (algebraMap ↥C_E B)
  haveI : IsLocalHom (algebraMap A ↥C_E₀) := by
    have : IsLocalHom ((algebraMap ↥C_E₀ B).comp (algebraMap A ↥C_E₀)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C_E₀ B]
    exact isLocalHom_of_comp _ (algebraMap ↥C_E₀ B)
  haveI : IsFractionRing ↥C_E ↥E := integralClosure.isFractionRing_of_finite_extension K ↥E
  haveI : IsFractionRing ↥C_E₀ ↥E₀ := integralClosure.isFractionRing_of_finite_extension K ↥E₀
  haveI : IsNoetherian A ↥C_E := IsIntegralClosure.isNoetherian A K ↥E C_E
  haveI : IsNoetherian A ↥C_E₀ := IsIntegralClosure.isNoetherian A K ↥E₀ C_E₀
  haveI : Module.Finite A ↥C_E := inferInstance
  haveI : Module.Finite A ↥C_E₀ := inferInstance
  haveI : FaithfulSMul ↥C_E B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_E B).mpr hinj_CE_B
  haveI : FaithfulSMul ↥C_E₀ B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_E₀ B).mpr hinj_CE₀_B
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C_E B := Algebra.IsIntegral.tower_top A
  haveI : Algebra.IsIntegral ↥C_E₀ B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C_E B) := Algebra.IsIntegral.isLocalHom ↥C_E B
  haveI : IsLocalHom (algebraMap ↥C_E₀ B) := Algebra.IsIntegral.isLocalHom ↥C_E₀ B
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E) (IsLocalRing.ResidueField B)
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) (IsLocalRing.ResidueField B)
  haveI : IsUnramifiedDVRExtension A ↥C_E :=
    isFiniteUnramifiedSubext_integralClosure_isUnramifiedDVR A K L E ⟨hE_fin, hE_unram⟩
  haveI : IsUnramifiedDVRExtension A ↥C_E₀ :=
    isFiniteUnramifiedSubext_integralClosure_isUnramifiedDVR A K L E₀ ⟨hE₀_fin, hE₀_unram⟩
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥C_E) ↥C_E :=
    integral_closure_isAdicComplete A K ↥E
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥C_E₀) ↥C_E₀ :=
    integral_closure_isAdicComplete A K ↥E₀
  haveI : HenselianLocalRing A :=
    dvr_extension_henselian A
  let f_E : IsLocalRing.ResidueField ↥C_E →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField B :=
    residueFieldFunctorAlg ι_E
  let f_E₀ : IsLocalRing.ResidueField ↥C_E₀ →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField B :=
    residueFieldFunctorAlg ι_E₀
  have hdeg_CE₀ : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) =
    Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
    have hdeg := IsUnramifiedDVRExtension.degree_eq (A := A) (B := ↥C_E₀)
    have hfund := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing ↥C_E₀ K ↥E₀
      (IsDiscreteValuationRing.not_a_field A)
    have hmap_eq : Ideal.map (algebraMap A ↥C_E₀) (IsLocalRing.maximalIdeal A) =
      IsLocalRing.maximalIdeal ↥C_E₀ :=
      Algebra.FormallyUnramified.map_maximalIdeal
    rw [← hmap_eq] at hfund
    have hmap_ne_top : Ideal.map (algebraMap A ↥C_E₀) (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
      rw [hmap_eq]; exact (IsLocalRing.maximalIdeal.isMaximal ↥C_E₀).ne_top
    have hmap_ne_bot : Ideal.map (algebraMap A ↥C_E₀) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
      rw [hmap_eq]; exact IsDiscreteValuationRing.not_a_field ↥C_E₀
    rw [Ideal.ramificationIdx_map_self_eq_one hmap_ne_top hmap_ne_bot, one_mul] at hfund
    rw [hmap_eq] at hfund
    rw [Ideal.inertiaDeg_algebraMap] at hfund
    change Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
    rw [show Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (↥C_E₀ ⧸ IsLocalRing.maximalIdeal ↥C_E₀) from rfl]
    rw [hfund, hE₀_deg]
  have hf_E₀_bij : Function.Bijective f_E₀ := by
    constructor
    · exact f_E₀.toRingHom.injective
    ·
      have hdim := hdeg_CE₀
      haveI : FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C_E₀) :=
        inferInstance
      haveI : FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
        inferInstance
      exact (f_E₀.toLinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
        f_E₀.toRingHom.injective
  let e_E₀ : IsLocalRing.ResidueField ↥C_E₀ ≃ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField B :=
    AlgEquiv.ofBijective f_E₀ hf_E₀_bij
  let f_res : IsLocalRing.ResidueField ↥C_E →ₐ[IsLocalRing.ResidueField A]
    IsLocalRing.ResidueField ↥C_E₀ :=
    e_E₀.symm.toAlgHom.comp f_E
  have hff := residueFieldFunctor_full_faithfulness (A := A) (B₁ := ↥C_E) (B₂ := ↥C_E₀)
  obtain ⟨φ, hφ⟩ := hff.2 f_res
  let ψ : ↥C_E →ₐ[A] B := ι_E₀.comp φ
  have hcompat : ψ = ι_E := by
    have hKrull : ⨅ i, (IsLocalRing.maximalIdeal B) ^ i = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
    apply Algebra.FormallyUnramified.ext_of_iInf (IsLocalRing.maximalIdeal B) hKrull
    intro y
    rw [Ideal.Quotient.eq]
    suffices h : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) (ψ y) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) (ι_E y) by
      exact Ideal.Quotient.eq.mp h
    change IsLocalRing.residue B (ι_E₀ (φ y)) = IsLocalRing.residue B (ι_E y)
    have h_ιE₀ : ∀ z, IsLocalRing.residue B (ι_E₀ z) =
      f_E₀ (IsLocalRing.residue ↥C_E₀ z) := fun z => by
      change IsLocalRing.residue B (ι_E₀ z) = (residueFieldFunctorAlg ι_E₀) (IsLocalRing.residue ↥C_E₀ z)
      rfl
    have h_ιE : ∀ w, IsLocalRing.residue B (ι_E w) =
      f_E (IsLocalRing.residue ↥C_E w) := fun w => by
      change IsLocalRing.residue B (ι_E w) = (residueFieldFunctorAlg ι_E) (IsLocalRing.residue ↥C_E w)
      rfl
    rw [h_ιE₀, h_ιE]
    have h_φ_res : IsLocalRing.residue ↥C_E₀ (φ y) =
      f_res (IsLocalRing.residue ↥C_E y) := by
      have : (residueFieldFunctorAlg φ) (IsLocalRing.residue ↥C_E y) =
        IsLocalRing.residue ↥C_E₀ (φ y) := rfl
      rw [← this, AlgHom.congr_fun hφ]
    rw [h_φ_res]
    simp only [f_res, AlgHom.coe_comp, Function.comp_apply, AlgEquiv.toAlgHom_eq_coe]
    show f_E₀ (e_E₀.symm (f_E (IsLocalRing.residue ↥C_E y))) =
      f_E (IsLocalRing.residue ↥C_E y)
    change e_E₀ (e_E₀.symm (f_E (IsLocalRing.residue ↥C_E y))) =
      f_E (IsLocalRing.residue ↥C_E y)
    exact AlgEquiv.apply_symm_apply e_E₀ _
  intro x hx
  set x' : ↥E := ⟨x, hx⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors C_E) x'
  set a₀ := φ a
  set b₀ := φ b
  have hcompat_fun : ∀ y : ↥C_E, ι_E y = ι_E₀ (φ y) := by
    intro y
    exact AlgHom.congr_fun hcompat.symm y
  have hι_E_comm : ∀ y : ↥C_E, algebraMap B L (ι_E y) = ι_E_L y :=
    fun y => IsIntegralClosure.algebraMap_lift A B L y
  have hι_E₀_comm : ∀ y : ↥C_E₀, algebraMap B L (ι_E₀ y) = ι_E₀_L y :=
    fun y => IsIntegralClosure.algebraMap_lift A B L y
  have hL_compat : ∀ y : ↥C_E, ι_E_L y = ι_E₀_L (φ y) := by
    intro y
    rw [← hι_E_comm, ← hι_E₀_comm, hcompat_fun]
  have hbL : ι_E₀_L b₀ ≠ 0 := by
    rw [← hL_compat b]
    intro h0
    have : (algebraMap ↥C_E ↥E b : L) = 0 := h0
    have hbE_zero : algebraMap ↥C_E ↥E b = 0 :=
      (FaithfulSMul.algebraMap_injective ↥E L) this
    exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ ((IsFractionRing.injective C_E ↥E) hbE_zero)
  have hab_L : x * ι_E_L b = ι_E_L a := by
    change (x' : L) * (algebraMap ↥E L (algebraMap ↥C_E ↥E b)) =
      algebraMap ↥E L (algebraMap ↥C_E ↥E a)
    have := congr_arg (algebraMap ↥E L) hab
    simp only [map_mul] at this
    convert this using 1
  have hab_E₀ : ι_E₀_L a₀ = x * ι_E₀_L b₀ := by
    rw [← hL_compat a, ← hL_compat b, hab_L]
  have ha₀_in_E₀ : ι_E₀_L a₀ ∈ E₀ :=
    (algebraMap ↥C_E₀ ↥E₀ a₀).2
  have hb₀_in_E₀ : ι_E₀_L b₀ ∈ E₀ :=
    (algebraMap ↥C_E₀ ↥E₀ b₀).2
  have hx_eq : x = ι_E₀_L a₀ * (ι_E₀_L b₀)⁻¹ := by
    have h1 : x * ι_E₀_L b₀ = ι_E₀_L a₀ := hab_E₀.symm
    field_simp at h1 ⊢
    exact h1
  rw [hx_eq]
  exact E₀.mul_mem ha₀_in_E₀ (E₀.inv_mem hb₀_in_E₀)

/--
[thm_10_13_unram_field_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_unram_field_embedding
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E E₀ : IntermediateField K L}
-- given
  (hE : IsFiniteUnramifiedSubext A K L E)
  (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
  (hE₀_deg : Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  ∃ ι : ↥E →ₐ[K] ↥E₀, ∀ (e : ↥E), (algebraMap ↥E₀ L (ι e) : L) = (algebraMap ↥E L e : L) := by
-- proof
  have hle : E ≤ E₀ := thm_10_13_unram_le E E₀ hE hE₀_unram hE₀_deg
  exact ⟨IntermediateField.inclusion hle, fun e => by
    simp only [IntermediateField.algebraMap_apply]
    exact congrArg Subtype.val (Subalgebra.inclusion_mk hle e.val e.property)⟩

/--
[thm_10_13_unram_subext_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_unram_subext_maximal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E₀ : IntermediateField K L}
-- given
  (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
  (hE₀_deg : Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  ∀ E : IntermediateField K L, IsFiniteUnramifiedSubext A K L E → E ≤ E₀ := by
-- proof
  intro E hE
  obtain ⟨ι, hι⟩ := thm_10_13_unram_field_embedding A K B L E E₀ hE hE₀_unram hE₀_deg
  intro x hxE
  have hcompat := hι ⟨x, hxE⟩
  rw [show (algebraMap ↥E L ⟨x, hxE⟩ : L) = x from rfl] at hcompat
  rw [← hcompat]
  exact (ι ⟨x, hxE⟩).property

/--
[AKLB_resDeg_over_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma AKLB_resDeg_over_eq_one
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E₀ : IntermediateField K L}
  [Algebra ↥(integralClosure A ↥E₀) B]
  [IsScalarTower A ↥(integralClosure A ↥E₀) B]
  [IsLocalHom (algebraMap ↥(integralClosure A ↥E₀) B)]
-- given
  (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
  (hE₀_deg : Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  let _instDVR := AKLB_intClE_isDVR A K L E₀ Module.finrank (IsLocalRing.ResidueField ↥(integralClosure A ↥E₀)) (IsLocalRing.ResidueField B) = 1 := by
-- proof
  intro _instDVR
  obtain ⟨hE₀_fin, hE₀_funram⟩ := hE₀_unram
  haveI hLC : IsLocalHom (algebraMap A ↥(integralClosure A ↥E₀)) := by
    have : IsLocalHom ((algebraMap ↥(integralClosure A ↥E₀) B).comp
      (algebraMap A ↥(integralClosure A ↥E₀))) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥(integralClosure A ↥E₀) B]
    exact isLocalHom_of_comp _ (algebraMap ↥(integralClosure A ↥E₀) B)
  haveI : (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E₀)).LiesOver
    (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : (IsLocalRing.maximalIdeal B).LiesOver
    (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E₀)) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  have htower := Ideal.inertiaDeg_algebra_tower
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E₀))
    (IsLocalRing.maximalIdeal B)
  rw [Ideal.inertiaDeg_algebraMap,
    Ideal.inertiaDeg_algebraMap (R := ↥(integralClosure A ↥E₀)) (S := B),
    Ideal.inertiaDeg_algebraMap (R := A) (S := ↥(integralClosure A ↥E₀))] at htower
  haveI : FiniteDimensional K ↥E₀ := hE₀_fin
  haveI : Algebra.IsSeparable K ↥E₀ := IntermediateField.isSeparable_tower_bot K E₀
  haveI : IsFractionRing ↥(integralClosure A ↥E₀) ↥E₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥E₀
  haveI : IsNoetherian A ↥(integralClosure A ↥E₀) :=
    IsIntegralClosure.isNoetherian A K ↥E₀ (integralClosure A ↥E₀)
  haveI : Module.Finite A ↥(integralClosure A ↥E₀) := inferInstance
  have hfund := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    ↥(integralClosure A ↥E₀) K ↥E₀
    (IsDiscreteValuationRing.not_a_field A)
  have hmap_eq : Ideal.map (algebraMap A ↥(integralClosure A ↥E₀))
    (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥(integralClosure A ↥E₀) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hmap_eq] at hfund
  have hmap_ne_top : Ideal.map (algebraMap A ↥(integralClosure A ↥E₀))
    (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap_eq]
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(integralClosure A ↥E₀)).ne_top
  have hmap_ne_bot : Ideal.map (algebraMap A ↥(integralClosure A ↥E₀))
    (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [hmap_eq]
    exact IsDiscreteValuationRing.not_a_field ↥(integralClosure A ↥E₀)
  rw [Ideal.ramificationIdx_map_self_eq_one hmap_ne_top hmap_ne_bot, one_mul] at hfund
  rw [hmap_eq] at hfund
  rw [Ideal.inertiaDeg_algebraMap] at hfund
  rw [hE₀_deg] at hfund
  rw [hfund] at htower
  have hf_pos : 0 < Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    Module.finrank_pos
  exact (Nat.mul_eq_left (Nat.pos_iff_ne_zero.mp hf_pos)).mp htower.symm

/--
[thm_10_13_totally_ramified_complement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_totally_ramified_complement
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {E₀ : IntermediateField K L}
-- given
  (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
  (hE₀_deg : Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  let _instDVR := AKLB_intClE_isDVR A K L E₀ ∃ (algOEB : Algebra ↥(integralClosure A ↥E₀) B) (_ : IsScalarTower A ↥(integralClosure A ↥E₀) B) (_ : IsLocalHom (@algebraMap ↥(integralClosure A ↥E₀) B _ _ algOEB)), Module.finrank (IsLocalRing.ResidueField ↥(integralClosure A ↥E₀)) (IsLocalRing.ResidueField B) = 1 := by
-- proof
  intro _instDVR
  set C := integralClosure A ↥E₀
  letI algCL : Algebra ↥C L :=
    ((E₀.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E₀.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI algOEB : Algebra ↥C B := φ.toAlgebra
  haveI hST : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective φ
    intro x y hxy
    have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
    apply_fun (algebraMap B L) at hxy
    rw [IsIntegralClosure.algebraMap_lift A B L x,
      IsIntegralClosure.algebraMap_lift A B L y] at hxy
    exact Subtype.val_injective (Subtype.val_injective hxy)
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI hLH : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  exact ⟨algOEB, hST, hLH,
    AKLB_resDeg_over_eq_one A K B L E₀ hE₀_unram hE₀_deg⟩

/--
[thm_10_13_maxUnram_eq_resDeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_13_maxUnram_eq_resDeg
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  ∃ (E₀ : IntermediateField K L), IsFiniteUnramifiedSubext A K L E₀ ∧ Module.finrank K E₀ = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) ∧ (∀ E : IntermediateField K L, IsFiniteUnramifiedSubext A K L E → E ≤ E₀) ∧ (let _instDVR := AKLB_intClE_isDVR A K L E₀; ∃ (algOEB : Algebra ↥(integralClosure A ↥E₀) B) (_ : IsScalarTower A ↥(integralClosure A ↥E₀) B) (_ : IsLocalHom (@algebraMap ↥(integralClosure A ↥E₀) B _ _ algOEB)), Module.finrank (IsLocalRing.ResidueField ↥(integralClosure A ↥E₀)) (IsLocalRing.ResidueField B) = 1) := by
-- proof
  obtain ⟨E₀, hE₀_unram, hE₀_deg⟩ := thm_10_13_exists_unram_subext_of_degree_f A K B L
  exact ⟨E₀, hE₀_unram, hE₀_deg,
    thm_10_13_unram_subext_maximal A K B L E₀ hE₀_unram hE₀_deg,
    thm_10_13_totally_ramified_complement A K B L E₀ hE₀_unram hE₀_deg⟩

/--
[thm_10_23_part_i](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_part_i
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  Module.finrank K (maximalUnramifiedSubextension A K L) = AKLB_resDeg A B := by
-- proof
  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L
  have hT_eq : maximalUnramifiedSubextension A K L = E₀ := by
    apply le_antisymm
    ·
      simp only [maximalUnramifiedSubextension]
      apply iSup_le; intro E; apply iSup_le; intro hE; exact hE₀_max E hE
    ·
      simp only [maximalUnramifiedSubextension]
      exact le_iSup₂ (f := fun (E : IntermediateField K L)
        (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  rwa [hT_eq]

/--
[thm_10_23_part_ii_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_part_ii_degree
-- imply
  Module.finrank (↥(maximalUnramifiedSubextension A K L)) L = AKLB_ramIdx A B := by
-- proof
  letI : FiniteDimensional K (↥(maximalUnramifiedSubextension A K L)) :=
    IntermediateField.finiteDimensional_left _
  letI : FiniteDimensional (↥(maximalUnramifiedSubextension A K L)) L :=
    IntermediateField.finiteDimensional_right _
  have hT := thm_10_23_part_i A K B L
  have htower := (Module.finrank_mul_finrank K
    (↥(maximalUnramifiedSubextension A K L)) L).symm
  have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [hef, hT] at htower
  have hf_pos : 0 < AKLB_resDeg A B := Module.finrank_pos
  rw [mul_comm (AKLB_ramIdx A B) (AKLB_resDeg A B)] at htower
  exact Nat.eq_of_mul_eq_mul_left hf_pos htower.symm

/--
[thm_10_23_part_ii_totally_ramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_part_ii_totally_ramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  let _instDVR := AKLB_intClE_isDVR A K L (maximalUnramifiedSubextension A K L) ∃ (algOEB : Algebra ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B) (_ : IsScalarTower A ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B) (_ : IsLocalHom (@algebraMap ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B _ _ algOEB)), Module.finrank (IsLocalRing.ResidueField ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L))) (IsLocalRing.ResidueField B) = 1 := by
-- proof
  intro _instDVR
  obtain ⟨E₀, _, _, hE₀_max, hE₀_ram⟩ := thm_10_13_maxUnram_eq_resDeg A K B L
  have hT_eq : maximalUnramifiedSubextension A K L = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ ‹_›
  subst hT_eq
  exact hE₀_ram

/--
[thm_10_23_part_iii_galois](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_part_iii_galois
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L] :
-- imply
  IsGalois K (maximalUnramifiedSubextension A K L) := by
-- proof
  rw [isGalois_iff]
  constructor
  · exact IntermediateField.isSeparable_tower_bot K (maximalUnramifiedSubextension A K L)
  · rw [IntermediateField.normal_iff_forall_map_eq']
    exact maximalUnramifiedSubextension_map_eq A K L

/--
[thm_10_23_galLK_eq_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_galLK_eq_decomp
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) = ⊤ := by
-- proof
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff]
  have : (σ • IsLocalRing.maximalIdeal B).IsMaximal := by
    rw [Ideal.pointwise_smul_eq_comap]
    exact Ideal.comap_isMaximal_of_equiv _
  exact IsLocalRing.eq_maximalIdeal this

/--
[smul_algebraMap_eq_galois](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma smul_algebraMap_eq_galois
  [Field K]
  [Field L]
  [Algebra K L]
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsFractionRing B L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  {σ : L ≃ₐ[K] L}
  {b : B} :
-- imply
  algebraMap B L (σ • b) = σ (algebraMap B L b) :=
-- proof
  algebraMap.smul' σ b L

/--
[dvr_card_inertia_subgroupOf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma dvr_card_inertia_subgroupOf_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)]
  {E : IntermediateField K L}
  [FiniteDimensional K E]
-- given
  (hunram : Algebra.FormallyUnramified A (integralClosure A E)) :
-- imply
  Nat.card (((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf E.fixingSubgroup) = Nat.card ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) := by
-- proof
  suffices h : (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  intro σ hσ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  set C := integralClosure A ↥E
  let ι_L : ↥C →ₐ[A] L := (E.val.restrictScalars A).comp C.val
  letI : Algebra ↥C L := ι_L.toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom ι_L
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let ι : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  let σ_B := MulSemiringAction.toAlgHom A B σ
  have hKrull : ⨅ i, (IsLocalRing.maximalIdeal B) ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
  have hext : σ_B.comp ι = ι := by
    apply Algebra.FormallyUnramified.ext_of_iInf (IsLocalRing.maximalIdeal B) hKrull
    intro y
    rw [Ideal.Quotient.eq]
    simp only [AlgHom.coe_comp, Function.comp_apply]
    exact hσ (ι y)
  have hfix_B : ∀ y : ↥C, σ • (ι y) = ι y := by
    intro y
    have := AlgHom.congr_fun hext y
    simp only [AlgHom.coe_comp, Function.comp_apply] at this
    exact this
  have hι_comm : ∀ y : ↥C, algebraMap B L (ι y) = ι_L y :=
    fun y => IsIntegralClosure.algebraMap_lift A B L y
  have hfix_L : ∀ y : ↥C, σ (ι_L y) = ι_L y := by
    intro y
    rw [← hι_comm, ← smul_algebraMap_eq_galois, hfix_B]
  haveI : IsFractionRing ↥C ↥E :=
    integralClosure.isFractionRing_of_finite_extension K ↥E
  set x' : ↥E := ⟨x, hx⟩
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors C) x'
  set aL := algebraMap ↥E L (algebraMap C ↥E a)
  set bL := algebraMap ↥E L (algebraMap C ↥E b)
  have haL : aL = ι_L a := rfl
  have hbL : bL = ι_L b := rfl
  have hab_L : x * bL = aL := by
    change (x' : L) * bL = aL
    have := congr_arg (algebraMap ↥E L) hab
    simp only [map_mul] at this
    convert this using 1
  have hσ_hab : σ x * bL = aL := by
    calc σ x * bL = σ x * σ bL := by rw [hbL, hfix_L b]
      _ = σ (x * bL) := by rw [map_mul]
      _ = σ aL := by rw [hab_L]
      _ = aL := by rw [haL, hfix_L a]
  have hb_ne : bL ≠ 0 := by
    intro h0
    have hbE_zero : algebraMap C ↥E b = 0 :=
      (FaithfulSMul.algebraMap_injective ↥E L) h0
    exact (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩) ((IsFractionRing.injective C ↥E) hbE_zero)
  exact mul_right_cancel₀ hb_ne (hσ_hab.trans hab_L.symm)

/--
[cor_7_14_inertia_le_fixingSubgroup_of_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma cor_7_14_inertia_le_fixingSubgroup_of_unramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)]
  {E : IntermediateField K L}
-- given
  (hfin : FiniteDimensional K E)
  (hunram : Algebra.FormallyUnramified A (integralClosure A E)) :
-- imply
  (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ≤ E.fixingSubgroup := by
-- proof
  haveI := hfin
  have hcard := dvr_card_inertia_subgroupOf_eq A K B L E hunram
  set H := (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)
  set K' := E.fixingSubgroup
  intro x hx
  let f : (H.subgroupOf K') → H := fun ⟨⟨g, _⟩, hg⟩ => ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
  have hf_inj : Function.Injective f := by
    intro ⟨⟨g₁, _⟩, _⟩ ⟨⟨g₂, _⟩, _⟩ heq
    simp only [f, Subtype.mk.injEq] at heq
    exact Subtype.ext (Subtype.ext heq)
  have hf_bij := hf_inj.bijective_of_nat_card_le (hcard ▸ le_refl _)
  obtain ⟨⟨⟨g, hg_K⟩, hg_H⟩, hg_eq⟩ := hf_bij.2 ⟨x, hx⟩
  simp only [f, Subtype.mk.injEq] at hg_eq
  rw [← hg_eq]; exact hg_K

/--
[cor_7_14_map_maximalIdeal_fixedField_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma cor_7_14_map_maximalIdeal_fixedField_inertia
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  let E := IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) let _instDVR := AKLB_intClE_isDVR A K L E Ideal.map (algebraMap A ↥(integralClosure A ↥E)) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal ↥(integralClosure A ↥E) := by
-- proof
  intro E _instDVR
  set C := integralClosure A (↥E) with hC_def
  haveI : FiniteDimensional K ↥E := IntermediateField.finiteDimensional_left E
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  letI algCL : Algebra ↥C L :=
    ((E.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  haveI : IsLocalHom (algebraMap A ↥C) := by
    have : IsLocalHom ((algebraMap ↥C B).comp (algebraMap A ↥C)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C B]
    exact isLocalHom_of_comp _ (algebraMap ↥C B)
  haveI hFU : Algebra.FormallyUnramified A ↥C :=
    formallyUnramified_integralClosure_of_complete_dvr A K ↥E
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥C := inferInstance
  haveI : Algebra.EssFiniteType A ↥C :=
    Algebra.EssFiniteType.of_finiteType A ↥C
  exact Algebra.FormallyUnramified.map_maximalIdeal

/--
[dvr_ramIdx_fixedField_inertia_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma dvr_ramIdx_fixedField_inertia_eq_one
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  let E := IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) let _instDVR := AKLB_intClE_isDVR A K L E (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E)) = 1 := by
-- proof
  intro E _instDVR
  set C := integralClosure A (↥E) with hC_def
  haveI : FiniteDimensional K ↥E := IntermediateField.finiteDimensional_left E
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  letI algCL : Algebra ↥C L :=
    ((E.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  haveI : IsLocalHom (algebraMap A ↥C) := by
    have : IsLocalHom ((algebraMap ↥C B).comp (algebraMap A ↥C)) := by
      rwa [← IsScalarTower.algebraMap_eq A ↥C B]
    exact isLocalHom_of_comp _ (algebraMap ↥C B)
  haveI : IsNoetherian A ↥C := IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥C := inferInstance
  haveI : Algebra.EssFiniteType A ↥C := Algebra.EssFiniteType.of_finiteType A ↥C
  have hmap_cor := cor_7_14_map_maximalIdeal_fixedField_inertia A K B L
  haveI : Algebra.FormallyUnramified A ↥C := by
    haveI : FaithfulSMul ↥C B := (faithfulSMul_iff_algebraMap_injective ↥C B).mpr (by
      change Function.Injective φ
      intro x y hxy
      apply_fun (algebraMap B L) at hxy
      rw [IsIntegralClosure.algebraMap_lift A B L x,
        IsIntegralClosure.algebraMap_lift A B L y] at hxy
      exact Subtype.val_injective (Subtype.val_injective hxy))
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
    haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
    haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) :=
      Algebra.isSeparable_tower_bot_of_isSeparable
        (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
    exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap_cor
  have hmap_eq : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥C :=
    Algebra.FormallyUnramified.map_maximalIdeal
  have hmap_ne_top : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊤ := by
    rw [hmap_eq]
    exact (IsLocalRing.maximalIdeal.isMaximal ↥C).ne_top
  have hmap_ne_bot : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [hmap_eq]
    exact IsDiscreteValuationRing.not_a_field ↥C
  have hram := Ideal.ramificationIdx_map_self_eq_one hmap_ne_top hmap_ne_bot
  rwa [hmap_eq] at hram

/--
[dvr_isSeparable_residueField_fixedField_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma dvr_isSeparable_residueField_fixedField_inertia
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [IsLocalHom (algebraMap A ↥(integralClosure A ↥(IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)))))] :
-- imply
  let E := IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) let _instDVR := AKLB_intClE_isDVR A K L E Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥(integralClosure A ↥E)) := by
-- proof
  intro E _instDVR
  set C := integralClosure A ↥E
  letI algCL : Algebra ↥C L :=
    ((E.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  haveI hlocal_C_B : IsLocalHom (algebraMap ↥C B) := by
    apply RingHom.IsIntegral.isLocalHom
    ·
      intro b
      have hAB : IsIntegral A b := IsIntegral.of_finite A b
      obtain ⟨p, hp_monic, hp_eval⟩ := hAB
      exact ⟨p.map (algebraMap A ↥C), hp_monic.map _, by
        rw [Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
        exact hp_eval⟩
    ·
      have hBL_inj : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
      have hCL_inj : Function.Injective (algebraMap ↥C L) := by
        change Function.Injective ((E.val.restrictScalars A).comp C.val)
        exact Subtype.val_injective.comp Subtype.val_injective
      have hfactor : ∀ c : ↥C, algebraMap B L (algebraMap ↥C B c) = algebraMap ↥C L c := by
        intro c
        show algebraMap B L (φ c) = ((E.val.restrictScalars A).comp C.val) c
        exact IsIntegralClosure.algebraMap_lift A B L c
      intro x y hxy
      apply hCL_inj
      rw [← hfactor, ← hfactor, hxy]
  exact Algebra.isSeparable_tower_bot_of_isSeparable
    (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField ↥C)
    (IsLocalRing.ResidueField B)

/--
[cor_7_14_fixedField_inertia_map_and_sep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma cor_7_14_fixedField_inertia_map_and_sep
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  let E := IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) let _instDVR := AKLB_intClE_isDVR A K L E ∃ (_ : IsLocalHom (algebraMap A ↥(integralClosure A ↥E))), Ideal.map (algebraMap A ↥(integralClosure A ↥E)) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal ↥(integralClosure A ↥E) ∧ Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥(integralClosure A ↥E)) := by
-- proof
  intro E _instDVR
  set C := integralClosure A ↥E
  letI algCL : Algebra ↥C L :=
    ((E.val.restrictScalars A).comp C.val).toAlgebra
  haveI : IsScalarTower A ↥C L :=
    IsScalarTower.of_algHom ((E.val.restrictScalars A).comp C.val)
  haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
  let φ : ↥C →ₐ[A] B := IsIntegralClosure.lift A B L
  letI : Algebra ↥C B := φ.toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom φ
  have hlocal_A_C : IsLocalHom (algebraMap A ↥C) := by
    have hcomp : (algebraMap ↥C B).comp (algebraMap A ↥C) = algebraMap A B := by
      ext a
      simp only [RingHom.comp_apply]
      exact (IsScalarTower.algebraMap_apply A ↥C B a).symm
    have : IsLocalHom ((algebraMap ↥C B).comp (algebraMap A ↥C)) := hcomp ▸ inferInstance
    exact isLocalHom_of_comp (algebraMap A ↥C) (algebraMap ↥C B)
  have hramIdx := dvr_ramIdx_fixedField_inertia_eq_one A K B L
  have hmap : Ideal.map (algebraMap A ↥C) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal ↥C := by
    haveI := hlocal_A_C
    exact map_maximalIdeal_eq_of_ramificationIdx_one A ↥C hramIdx
  haveI := hlocal_A_C
  have hsep := dvr_isSeparable_residueField_fixedField_inertia A K B L
  exact ⟨hlocal_A_C, hmap, hsep⟩

/--
[cor_7_14_fixedField_inertia_formallyUnramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma cor_7_14_fixedField_inertia_formallyUnramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  Algebra.FormallyUnramified A (integralClosure A (IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)))) := by
-- proof
  set E := IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L))
  haveI : IsDiscreteValuationRing ↥(integralClosure A ↥E) := AKLB_intClE_isDVR A K L E
  obtain ⟨hLH, hmap, hsep⟩ := cor_7_14_fixedField_inertia_map_and_sep A K B L
  haveI := hLH
  haveI := hsep
  haveI : IsNoetherian A ↥(integralClosure A ↥E) :=
    IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥(integralClosure A ↥E) := inferInstance
  haveI : Algebra.EssFiniteType A ↥(integralClosure A ↥E) :=
    Algebra.EssFiniteType.of_finiteType A ↥(integralClosure A ↥E)
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmap

/--
[formallyUnramified_le_fixedField_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma formallyUnramified_le_fixedField_inertia
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)]
  {E : IntermediateField K L}
-- given
  (hE : IsFiniteUnramifiedSubext A K L E) :
-- imply
  E ≤ IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) := by
-- proof
  obtain ⟨hfin, hunram⟩ := hE
  have hle := cor_7_14_inertia_le_fixingSubgroup_of_unramified A K B L E hfin hunram
  exact (IntermediateField.le_iff_le
    ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) E).mpr hle

/--
[fixedField_inertia_formallyUnramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma fixedField_inertia_formallyUnramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B] :
-- imply
  IsFiniteUnramifiedSubext A K L (IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L))) := by
-- proof
  constructor
  ·
    exact IntermediateField.finiteDimensional_left _
  ·
    exact cor_7_14_fixedField_inertia_formallyUnramified A K B L

/--
[fixedField_inertia_eq_maxUnram](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma fixedField_inertia_eq_maxUnram
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)] :
-- imply
  IntermediateField.fixedField ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)) = maximalUnramifiedSubextension A K L := by
-- proof
  apply le_antisymm
  ·
    have hunram := fixedField_inertia_formallyUnramified A K B L
    show IntermediateField.fixedField _ ≤ maximalUnramifiedSubextension A K L
    unfold maximalUnramifiedSubextension
    exact le_iSup₂_of_le _ hunram (le_refl _)
  ·
    show maximalUnramifiedSubextension A K L ≤ IntermediateField.fixedField _
    unfold maximalUnramifiedSubextension
    exact iSup₂_le (fun E hE => formallyUnramified_le_fixedField_inertia A K B L E hE)

/--
[thm_10_23_galLE_eq_inertia](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_galLE_eq_inertia
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)] :
-- imply
  (maximalUnramifiedSubextension A K L).fixingSubgroup = (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) := by
-- proof
  rw [← IsGalois.fixedField_eq_iff_fixingSubgroup_eq]
  exact fixedField_inertia_eq_maxUnram A K B L

/--
[thm_10_23_galEK_iso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23_galEK_iso
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsGalois K L]
  [MulSemiringAction (L ≃ₐ[K] L) B]
  [SMulDistribClass (L ≃ₐ[K] L) B L]
  [SMulCommClass (L ≃ₐ[K] L) A B]
  [Algebra.IsInvariant A B (L ≃ₐ[K] L)] :
-- imply
  Nonempty ((↥(maximalUnramifiedSubextension A K L) ≃ₐ[K] ↥(maximalUnramifiedSubextension A K L)) ≃* (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField B)) := by
-- proof
  haveI hGalEK : IsGalois K (maximalUnramifiedSubextension A K L) :=
    thm_10_23_part_iii_galois A K B L
  set E := maximalUnramifiedSubextension A K L
  have hFix : IntermediateField.fixedField E.fixingSubgroup = E :=
    IsGalois.fixedField_fixingSubgroup E
  haveI hNormal : E.fixingSubgroup.Normal := inferInstance
  have hInertia : E.fixingSubgroup =
    (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) :=
    thm_10_23_galLE_eq_inertia A K B L
  have hDecomp : MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) = ⊤ :=
    thm_10_23_galLK_eq_decomp A K B L
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI hInertNormal : ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).Normal := by
    rw [← hInertia]; exact hNormal
  let iso1 : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup ≃* (↥E ≃ₐ[K] ↥E) := by
    have h := IsGalois.normalAutEquivQuotient E.fixingSubgroup
    rw [hFix] at h; exact h
  let iso3 := Ideal.Quotient.stabilizerQuotientInertiaEquiv
    (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  let iso2a : (L ≃ₐ[K] L) ⧸ E.fixingSubgroup ≃*
    (L ≃ₐ[K] L) ⧸ (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) :=
    QuotientGroup.quotientMulEquivOfEq hInertia
  haveI : ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf
    (⊤ : Subgroup (L ≃ₐ[K] L)) |>.Normal := hInertNormal.subgroupOf ⊤
  let iso2b_f : (⊤ : Subgroup (L ≃ₐ[K] L)) →* (L ≃ₐ[K] L) ⧸
    (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) :=
    (QuotientGroup.mk' _).comp (Subgroup.subtype ⊤)
  have iso2b_ker : iso2b_f.ker =
    ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf ⊤ := by
    ext ⟨x, _⟩; simp [iso2b_f, QuotientGroup.eq_one_iff]
  have iso2b_surj : Function.Surjective iso2b_f := by
    intro q; exact q.inductionOn' (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
  let iso2b : (L ≃ₐ[K] L) ⧸ (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ≃*
    ↥(⊤ : Subgroup (L ≃ₐ[K] L)) ⧸
      ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf ⊤ :=
    ((QuotientGroup.quotientMulEquivOfEq iso2b_ker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective iso2b_f iso2b_surj)).symm
  haveI : ((IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L)).subgroupOf
    (MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B)) |>.Normal := by
    rw [hDecomp]; exact hInertNormal.subgroupOf ⊤
  let iso2c := QuotientGroup.equivQuotientSubgroupOfOfEq
    (A' := (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L))
    (B' := (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L))
    (A := ⊤)
    (B := MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B))
    rfl hDecomp.symm
  exact ⟨iso1.symm.trans (iso2a.trans (iso2b.trans (iso2c.trans iso3)))⟩

/--
[thm_10_23](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm1023.lean)
-/
@[path]
lemma thm_10_23
  [IsGalois K L] :
-- imply
  let _intCl : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed B A L let _act : MulSemiringAction (L ≃ₐ[K] L) B := IsIntegralClosure.MulSemiringAction A K L B Module.finrank K (maximalUnramifiedSubextension A K L) = AKLB_resDeg A B ∧ Module.finrank (↥(maximalUnramifiedSubextension A K L)) L = AKLB_ramIdx A B ∧ (let _instDVR := AKLB_intClE_isDVR A K L (maximalUnramifiedSubextension A K L) ∃ (algOEB : Algebra ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B) (_ : IsScalarTower A ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B) (_ : IsLocalHom (@algebraMap ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L)) B _ _ algOEB)), Module.finrank (IsLocalRing.ResidueField ↥(integralClosure A ↥(maximalUnramifiedSubextension A K L))) (IsLocalRing.ResidueField B) = 1) ∧ IsGalois K (maximalUnramifiedSubextension A K L) ∧ MulAction.stabilizer (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal B) = ⊤ ∧ (maximalUnramifiedSubextension A K L).fixingSubgroup = (IsLocalRing.maximalIdeal B).inertia (L ≃ₐ[K] L) ∧ Nonempty ((↥(maximalUnramifiedSubextension A K L) ≃ₐ[K] ↥(maximalUnramifiedSubextension A K L)) ≃* (IsLocalRing.ResidueField B ≃ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField B)) := by
-- proof
  haveI : IsIntegralClosure B A L := IsIntegralClosure.of_isIntegrallyClosed B A L
  letI : MulSemiringAction (L ≃ₐ[K] L) B := IsIntegralClosure.MulSemiringAction A K L B
  haveI : SMulDistribClass (L ≃ₐ[K] L) B L := inferInstance
  haveI : SMulCommClass (L ≃ₐ[K] L) A B :=
    ⟨fun σ a b => by
      show (galRestrict A K L B σ) (a • b) = a • ((galRestrict A K L B σ) b)
      simp only [Algebra.smul_def, map_mul, AlgEquiv.commutes]⟩
  haveI : Algebra.IsInvariant A B (L ≃ₐ[K] L) := Algebra.isInvariant_of_isGalois A K L B
  exact ⟨thm_10_23_part_i A K B L, thm_10_23_part_ii_degree A K B L,
    thm_10_23_part_ii_totally_ramified A K B L,
    thm_10_23_part_iii_galois A K B L,
    thm_10_23_galLK_eq_decomp A K B L,
    thm_10_23_galLE_eq_inertia A K B L,
    thm_10_23_galEK_iso A K B L⟩


-- created on 2026-10-23
