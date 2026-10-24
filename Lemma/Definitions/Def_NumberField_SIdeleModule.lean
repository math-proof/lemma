import Mathlib
import Lemma.Definitions.Def_GroupCohomology_RepPi
import Lemma.Definitions.Def_GroupCohomology_RepCokernel
import Lemma.Definitions.Def_NumberField_SIdeleClassModule
import Lemma.Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

namespace NumberField.SIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev locInf (v : InfinitePlace E) : K →+* (NumberField.ArchIdele.above E K v).Completion := algebraMap K _

theorem locInf_apply (v : InfinitePlace E) (x : K) :
    locInf E K v x = ((WithAbs.equiv (NumberField.ArchIdele.above E K v).1).symm x : (NumberField.ArchIdele.above E K v).Completion) := rfl

theorem smul_locInf (v : InfinitePlace E) (σ : NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) (x : K) :
    σ • locInf E K v x = locInf E K v ((σ : K ≃ₐ[E] K) x) := by
  rw [NumberField.InfPlaceDecomp.smul_def, locInf_apply, locInf_apply, NumberField.InfPlaceDecomp.actRingEquiv_coe, WithAbs.congr_apply]
  rfl

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable def diagFunInf (v : InfinitePlace E) :
    NumberField.SUnits.sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((NumberField.ArchIdele.above E K v).Completion)ˣ) where
  toFun x g := Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x))
  map_add' x y := by
    funext g
    change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • (NumberField.SUnits.val E K S x * NumberField.SUnits.val E K S y))) = _
    rw [smul_mul', map_mul, ofMul_mul]
    rfl
  map_smul' n x := by
    funext g
    change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • (NumberField.SUnits.val E K S x ^ n))) = _
    rw [smul_zpow', map_zpow, ofMul_zpow]
    rfl

theorem diagFunInf_apply (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    diagFunInf E K S v x g = Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x)) := rfl

theorem diagFunInf_mem_coindV (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) :
    diagFunInf E K S v x ∈ Representation.coindV (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
      (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)).ρ := by
  intro d h
  change Additive.ofMul (Units.map (locInf E K v).toMonoidHom (((d : K ≃ₐ[E] K) * h) • NumberField.SUnits.val E K S x)) =
    Additive.ofMul (d • Units.map (locInf E K v).toMonoidHom (h • NumberField.SUnits.val E K S x))
  rw [mul_smul]
  congr 1
  ext : 1
  exact (smul_locInf E K v d _).symm

noncomputable def diagInf (v : InfinitePlace E) :
    NumberField.SUnits.sUnitsRep E K S ⟶ NumberField.ArchIdele.fibre E K v :=
  Rep.ofHom ⟨(diagFunInf E K S v).codRestrict _ (diagFunInf_mem_coindV E K S v), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFunInf E K S v ((NumberField.SUnits.sUnitsRep E K S).ρ g x) h = diagFunInf E K S v x (h * g)
      rw [diagFunInf_apply, diagFunInf_apply, NumberField.SUnits.val_rho, mul_smul])⟩

theorem diagInf_hom_apply_apply (v : InfinitePlace E) (x : NumberField.SUnits.sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    ((diagInf E K S v).hom x).1 g = Additive.ofMul (Units.map (locInf E K v).toMonoidHom (g • NumberField.SUnits.val E K S x)) := rfl

abbrev Index : Type := NumberField.FiniteSIdele.Index E S ⊕ InfinitePlace E

noncomputable def fibre : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (NumberField.FiniteSIdele.fibre E K S) (NumberField.ArchIdele.fibre E K)

@[simp] theorem fibre_inl (i : NumberField.FiniteSIdele.Index E S) : fibre E K S (Sum.inl i) = NumberField.FiniteSIdele.fibre E K S i := rfl

@[simp] theorem fibre_inr (v : InfinitePlace E) : fibre E K S (Sum.inr v) = NumberField.ArchIdele.fibre E K v := rfl

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K S)

noncomputable def toFinite : obj E K S ⟶ NumberField.FiniteSIdele.obj E K S :=
  GroupCohomology.RepPi.lift _ fun i => GroupCohomology.RepPi.proj (fibre E K S) (Sum.inl i)

noncomputable def toArch : obj E K S ⟶ NumberField.ArchIdele.obj E K :=
  GroupCohomology.RepPi.lift _ fun v => GroupCohomology.RepPi.proj (fibre E K S) (Sum.inr v)

@[simp] theorem toFinite_hom_apply (x : obj E K S) (i : NumberField.FiniteSIdele.Index E S) : (toFinite E K S).hom x i = x (Sum.inl i) := rfl

@[simp] theorem toArch_hom_apply (x : obj E K S) (v : InfinitePlace E) : (toArch E K S).hom x v = x (Sum.inr v) := rfl

noncomputable def diagComponent : (i : Index E S) → (NumberField.SUnits.sUnitsRep E K S ⟶ fibre E K S i)
  | Sum.inl i => NumberField.SUnits.diagComponent E K S i
  | Sum.inr v => diagInf E K S v

noncomputable def diag : NumberField.SUnits.sUnitsRep E K S ⟶ obj E K S :=
  GroupCohomology.RepPi.lift (fibre E K S) (diagComponent E K S)

theorem diag_hom_apply_inl (x : NumberField.SUnits.sUnitsRep E K S) (i : NumberField.FiniteSIdele.Index E S) :
    (diag E K S).hom x (Sum.inl i) = (NumberField.SUnits.diagComponent E K S i).hom x := rfl

theorem diag_hom_apply_inr (x : NumberField.SUnits.sUnitsRep E K S) (v : InfinitePlace E) :
    (diag E K S).hom x (Sum.inr v) = (diagInf E K S v).hom x := rfl

theorem diag_toFinite : diag E K S ≫ toFinite E K S = NumberField.SUnits.diag E K S :=
  GroupCohomology.RepPi.hom_ext _ fun i => by
    cases i <;> rfl

noncomputable abbrev classObj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepCokernel.obj (diag E K S)

noncomputable abbrev toClass : obj E K S ⟶ classObj E K S := GroupCohomology.RepCokernel.π (diag E K S)

theorem toClass_hom_apply_eq_zero_iff (y : obj E K S) :
    (toClass E K S).hom y = 0 ↔ y ∈ Set.range (diag E K S).hom :=
  GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff (diag E K S) y

noncomputable abbrev classSeq : ShortComplex (Rep ℤ (K ≃ₐ[E] K)) := GroupCohomology.RepCokernel.seq (diag E K S)

end NumberField.SIdele
