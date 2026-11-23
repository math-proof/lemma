module

public import Mathlib
public import Theorem.Rep.RepPi
public import Theorem.Matrix.PlaceAbove
public import Theorem.Valuation.PlaceDecompositionAction
public import Abbrev.NumberField_FiniteSIdeleModule
public import Theorem.Rep.SUnitsModule
public import Def.GroupCohomology_RepCokernel

public section

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory Matrix Valuation Rep
open scoped NumberField.PlaceDecomp

namespace NumberField.SUnits

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

section units
variable {E K}


@[simp] public theorem coe_unitOfValuedEqOne (w : HeightOneSpectrum (𝓞 K)) (a : w.adicCompletion K) (ha : Valued.v a = 1) :
    ((unitOfValuedEqOne w a ha : w.adicCompletionIntegers K) : w.adicCompletion K) = a := rfl

set_option synthInstance.maxHeartbeats 200000 in


public theorem coe_coe_zpow (w : HeightOneSpectrum (𝓞 K)) (u : (w.adicCompletionIntegers K)ˣ) (n : ℤ) :
    (((u ^ n : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) =
      ((u : w.adicCompletionIntegers K) : w.adicCompletion K) ^ n := by
  change ((Units.map (w.adicCompletionIntegers K).subtype.toMonoidHom (u ^ n) :
      (w.adicCompletion K)ˣ) : w.adicCompletion K) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl


public theorem coe_unitOfValuedEqOne_zpow (w : HeightOneSpectrum (𝓞 K)) (a : w.adicCompletion K) (ha : Valued.v a = 1) (n : ℤ) :
    (((unitOfValuedEqOne w a ha ^ n : (w.adicCompletionIntegers K)ˣ) : w.adicCompletionIntegers K) : w.adicCompletion K) = a ^ n :=
  coe_coe_zpow w _ n

end units

variable (S : Finset (HeightOneSpectrum (𝓞 E)))


public theorem diagFun_mem_coindV (v : HeightOneSpectrum (𝓞 E)) (x : sUnitsRep E K S) :
    diagFun E K S v x ∈ Representation.coindV (FiniteSIdele.D E K v).subtype (FiniteSIdele.localUnits E K v).ρ := by
  intro d h
  change Additive.ofMul (Units.map (loc E K v).toMonoidHom (((d : K ≃ₐ[E] K) * h) • val E K S x)) =
    Additive.ofMul (d • Units.map (loc E K v).toMonoidHom (h • val E K S x))
  rw [mul_smul]
  congr 1
  refine Units.ext ?_
  exact (smul_loc E K v d _).symm


public theorem diagIn_hom_apply_apply (v : {v // v ∈ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    ((diagIn E K S v).hom x).1 g = Additive.ofMul (Units.map (loc E K v.1).toMonoidHom (g • val E K S x)) := rfl


public theorem valued_loc_smul_val (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    Valued.v (loc E K v.1 ((g • val E K S x : Kˣ) : K)) = 1 := by
  rw [valued_loc]
  exact valuation_eq_one_of_mem_sUnits E K S (val_mem E K S x) g v.2


public theorem diagFunOut_apply_coe (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    (((Additive.toMul (diagFunOut E K S v x g) : ((Matrix.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
      (Matrix.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (Matrix.PlaceAbove.above E K v.1).adicCompletion K) =
      loc E K v.1 ((g • val E K S x : Kˣ) : K) := rfl


public theorem diagFunOut_mem_coindV (v : {v // v ∉ S}) (x : sUnitsRep E K S) :
    diagFunOut E K S v x ∈ Representation.coindV (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localIntegerUnits E K v.1).ρ := by
  intro d h
  change diagFunOut E K S v x ((d : K ≃ₐ[E] K) * h) = Additive.ofMul (d • Additive.toMul (diagFunOut E K S v x h))
  refine congrArg Additive.ofMul (Units.ext (Subtype.ext ?_))
  change loc E K v.1 ((((d : K ≃ₐ[E] K) * h) • val E K S x : Kˣ) : K) = d • loc E K v.1 ((h • val E K S x : Kˣ) : K)
  rw [mul_smul, smul_loc]
  rfl


public theorem diagOut_hom_apply_apply_coe (v : {v // v ∉ S}) (x : sUnitsRep E K S) (g : K ≃ₐ[E] K) :
    (((Additive.toMul (((diagOut E K S v).hom x).1 g) : ((Matrix.PlaceAbove.above E K v.1).adicCompletionIntegers K)ˣ) :
      (Matrix.PlaceAbove.above E K v.1).adicCompletionIntegers K) : (Matrix.PlaceAbove.above E K v.1).adicCompletion K) =
      loc E K v.1 ((g • val E K S x : Kˣ) : K) := rfl


public theorem diag_hom_apply_inl (x : sUnitsRep E K S) (v : {v // v ∈ S}) : (diag E K S).hom x (Sum.inl v) = (diagIn E K S v).hom x := rfl


public theorem diag_hom_apply_inr (x : sUnitsRep E K S) (v : {v // v ∉ S}) : (diag E K S).hom x (Sum.inr v) = (diagOut E K S v).hom x := rfl


public theorem toSClass_hom_apply_eq_zero_iff (y : FiniteSIdele.obj E K S) :
    (toSClass E K S).hom y = 0 ↔ y ∈ Set.range (diag E K S).hom :=
  GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff (diag E K S) y

