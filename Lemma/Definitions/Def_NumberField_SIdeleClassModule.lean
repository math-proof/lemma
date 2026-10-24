import Mathlib
import Lemma.Definitions.Def_GroupCohomology_RepPi
import Lemma.Definitions.Def_NumberField_PlaceAbove
import Lemma.Definitions.Def_NumberField_PlaceDecompositionAction
import Lemma.Definitions.Def_NumberField_FiniteSIdeleModule
import Lemma.Definitions.Def_NumberField_SUnitsModule
import Lemma.Definitions.Def_GroupCohomology_RepCokernel

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

section units
variable {E K}

noncomputable def unitOfValuedEqOne (w : HeightOneSpectrum (𝓞 K)) (a : w.adicCompletion K) (ha : Valued.v a = 1) :
    (w.adicCompletionIntegers K)ˣ :=
  have ha0 : a ≠ 0 := fun h => by rw [h, Valuation.map_zero] at ha; exact zero_ne_one ha
  { val := ⟨a, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K w).2 ha.le⟩
    inv := ⟨a⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K w).2 (by rw [Valuation.map_inv, ha, inv_one])⟩
    val_inv := Subtype.ext (mul_inv_cancel₀ ha0)
    inv_val := Subtype.ext (inv_mul_cancel₀ ha0) }

@[simp] theorem coe_unitOfValuedEqOne (w : HeightOneSpectrum (𝓞 K)) (a : w.adicCompletion K) (ha : Valued.v a = 1) :
    ((unitOfValuedEqOne w a ha : w.adicCompletionIntegers K) : w.adicCompletion K) = a := rfl

set_option synthInstance.maxHeartbeats 200000 in

theorem coe_coe_zpow (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletionIntegers K)ˣ) (n : ℤ) :
    (((u ^ n : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) =
      ((u : w.adicCompletionIntegers K) : w.adicCompletion K) ^ n := by
  change ((Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom (u ^ n) :
      (w.adicCompletion K)ˣ) : w.adicCompletion K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem coe_unitOfValuedEqOne_zpow (w : HeightOneSpectrum (𝓞 K)) (a : w.adicCompletion K) (ha : Valued.v a = 1) (n : ℤ) :
    (((unitOfValuedEqOne w a ha ^ n : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) = a ^ n :=
  coe_coe_zpow w _ n

end units

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

theorem diagFun_mem_coindV (v : HeightOneSpectrum (𝓞 E)) (x : sUnitsRep E K S) :
    diagFun E K S v x ∈ Representation.coindV (FiniteSIdele.D E K v).subtype (FiniteSIdele.localUnits E K v).ρ := by
  intro d h
  change Additive.ofMul (Units.map (loc E K v).toMonoidHom (((d : K ≃ₐ[E] K) * h) • val E K S x)) =
    Additive.ofMul (d • Units.map (loc E K v).toMonoidHom (h • val E K S x))
  rw [mul_smul]
  congr 1
  refine Units.ext ?_
  exact (smul_loc E K v d _).symm

noncomputable def diagIn (v : {v // v ∈ S}) :
    sUnitsRep E K S ⟶ Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localUnits E K v.1) :=
  Rep.ofHom ⟨(diagFun E K S v.1).codRestrict _ (diagFun_mem_coindV E K S v.1), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFun E K S v.1 ((sUnitsRep E K S).ρ g x) h = diagFun E K S v.1 x (h * g)
      rw [diagFun_apply, diagFun_apply, val_rho, mul_smul])⟩

theorem diagIn_hom_apply_apply (v : {v // v ∈ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    ((diagIn E K S v).hom x).1 g = Additive.ofMul (Units.map (loc E K v.1).toMonoidHom (g • val E K S x)) := rfl

theorem valued_loc_smul_val (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    Valued.v (loc E K v.1 ((g • val E K S x : Kˣ) : K)) = 1 := by
  rw [valued_loc]
  exact valuation_eq_one_of_mem_sUnits E K S (val_mem E K S x) g v.2

noncomputable def diagFunOut (v : {v // v ∉ S}) :
    sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) where
  toFun x g := Additive.ofMul (unitOfValuedEqOne _ (loc E K v.1 ((g • val E K S x : Kˣ) : K)) (valued_loc_smul_val E K S v x g))
  map_add' x y := by
    funext g
    change Additive.ofMul (unitOfValuedEqOne _ (loc E K v.1 ((g • (val E K S x * val E K S y) : Kˣ) : K)) _) =
      Additive.ofMul (unitOfValuedEqOne _ _ (valued_loc_smul_val E K S v x g) * unitOfValuedEqOne _ _ (valued_loc_smul_val E K S v y g))
    refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
    change loc E K v.1 ((g • (val E K S x * val E K S y) : Kˣ) : K) =
      loc E K v.1 ((g • val E K S x : Kˣ) : K) * loc E K v.1 ((g • val E K S y : Kˣ) : K)
    rw [smul_mul', Units.val_mul, map_mul]
  map_smul' n x := by
    funext g
    change Additive.ofMul (unitOfValuedEqOne _ (loc E K v.1 ((g • (val E K S x ^ n) : Kˣ) : K)) _) =
      Additive.ofMul (unitOfValuedEqOne _ _ (valued_loc_smul_val E K S v x g) ^ n)
    refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
    rw [coe_unitOfValuedEqOne_zpow]
    change loc E K v.1 ((g • (val E K S x ^ n) : Kˣ) : K) = loc E K v.1 ((g • val E K S x : Kˣ) : K) ^ n
    rw [smul_zpow', Units.val_zpow_eq_zpow_val, map_zpow₀]

theorem diagFunOut_apply_coe (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    (((Additive.toMul (diagFunOut E K S v x g) : ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
      (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K) =
      loc E K v.1 ((g • val E K S x : Kˣ) : K) := rfl

theorem diagFunOut_mem_coindV (v : {v // v ∉ S}) (x : sUnitsRep E K S) :
    diagFunOut E K S v x ∈ Representation.coindV (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localIntegerUnits E K v.1).ρ := by
  intro d h
  change diagFunOut E K S v x ((d : K ≃ₐ[E] K) * h) = Additive.ofMul (d • Additive.toMul (diagFunOut E K S v x h))
  refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
  change loc E K v.1 ((((d : K ≃ₐ[E] K) * h) • val E K S x : Kˣ) : K) = d • loc E K v.1 ((h • val E K S x : Kˣ) : K)
  rw [mul_smul, smul_loc]
  rfl

noncomputable def diagOut (v : {v // v ∉ S}) :
    sUnitsRep E K S ⟶ Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localIntegerUnits E K v.1) :=
  Rep.ofHom ⟨(diagFunOut E K S v).codRestrict _ (diagFunOut_mem_coindV E K S v), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFunOut E K S v ((sUnitsRep E K S).ρ g x) h = diagFunOut E K S v x (h * g)
      refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
      change loc E K v.1 ((h • val E K S ((sUnitsRep E K S).ρ g x) : Kˣ) : K) = loc E K v.1 (((h * g) • val E K S x : Kˣ) : K)
      rw [val_rho, mul_smul])⟩

theorem diagOut_hom_apply_apply_coe (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    (((Additive.toMul (((diagOut E K S v).hom x).1 g) : ((NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
      (NumberField.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (NumberField.PlaceAbove.above E K v.1).adicCompletion K) =
      loc E K v.1 ((g • val E K S x : Kˣ) : K) := rfl

noncomputable def diagComponent : (i : FiniteSIdele.Index E S) → (sUnitsRep E K S ⟶ FiniteSIdele.fibre E K S i)
  | Sum.inl v => diagIn E K S v
  | Sum.inr v => diagOut E K S v

noncomputable def diag : sUnitsRep E K S ⟶ FiniteSIdele.obj E K S :=
  GroupCohomology.RepPi.lift (FiniteSIdele.fibre E K S) (diagComponent E K S)

theorem diag_hom_apply_inl (x : sUnitsRep E K S) (v : {v // v ∈ S}) : (diag E K S).hom x (Sum.inl v) = (diagIn E K S v).hom x := rfl

theorem diag_hom_apply_inr (x : sUnitsRep E K S) (v : {v // v ∉ S}) : (diag E K S).hom x (Sum.inr v) = (diagOut E K S v).hom x := rfl

noncomputable abbrev sClassObj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepCokernel.obj (diag E K S)

noncomputable abbrev toSClass : FiniteSIdele.obj E K S ⟶ sClassObj E K S := GroupCohomology.RepCokernel.π (diag E K S)

theorem toSClass_hom_apply_eq_zero_iff (y : FiniteSIdele.obj E K S) :
    (toSClass E K S).hom y = 0 ↔ y ∈ Set.range (diag E K S).hom :=
  GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff (diag E K S) y

noncomputable abbrev sClassSeq : ShortComplex (Rep ℤ (K ≃ₐ[E] K)) := GroupCohomology.RepCokernel.seq (diag E K S)

end NumberField.SUnits
