import Mathlib
import Def.Rep_RepPi
import Theorem.Matrix.PlaceAbove
import Def.NumberField_PlaceDecompositionAction
import Abbrev.NumberField_FiniteSIdeleModule
import Def.NumberField_SUnitsModule
import Def.GroupCohomology_RepCokernel

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory Matrix Valuation Rep
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


end units

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable def diagIn (v : {v // v ∈ S}) :
    sUnitsRep E K S ⟶ Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localUnits E K v.1) :=
  Rep.ofHom ⟨(diagFun E K S v.1).codRestrict _ (diagFun_mem_coindV E K S v.1), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFun E K S v.1 ((sUnitsRep E K S).ρ g x) h = diagFun E K S v.1 x (h * g)
      rw [diagFun_apply, diagFun_apply, val_rho, mul_smul])⟩

noncomputable def diagFunOut (v : {v // v ∉ S}) :
    sUnitsRep E K S →ₗ[ℤ] ((K ≃ₐ[E] K) → Additive ((Matrix.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) where
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

noncomputable def diagOut (v : {v // v ∉ S}) :
    sUnitsRep E K S ⟶ Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localIntegerUnits E K v.1) :=
  Rep.ofHom ⟨(diagFunOut E K S v).codRestrict _ (diagFunOut_mem_coindV E K S v), fun g => LinearMap.ext fun x =>
    Subtype.ext (funext fun h => by
      change diagFunOut E K S v ((sUnitsRep E K S).ρ g x) h = diagFunOut E K S v x (h * g)
      refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
      change loc E K v.1 ((h • val E K S ((sUnitsRep E K S).ρ g x) : Kˣ) : K) = loc E K v.1 (((h * g) • val E K S x : Kˣ) : K)
      rw [val_rho, mul_smul])⟩

noncomputable def diagComponent : (i : FiniteSIdele.Index E S) → (sUnitsRep E K S ⟶ FiniteSIdele.fibre E K S i)
  | Sum.inl v => diagIn E K S v
  | Sum.inr v => diagOut E K S v

noncomputable def diag : sUnitsRep E K S ⟶ FiniteSIdele.obj E K S :=
  Rep.RepPi.lift (FiniteSIdele.fibre E K S) (diagComponent E K S)

noncomputable abbrev sClassObj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepCokernel.obj (diag E K S)

noncomputable abbrev toSClass : FiniteSIdele.obj E K S ⟶ sClassObj E K S := GroupCohomology.RepCokernel.π (diag E K S)

noncomputable abbrev sClassSeq : ShortComplex (Rep ℤ (K ≃ₐ[E] K)) := GroupCohomology.RepCokernel.seq (diag E K S)

end NumberField.SUnits
