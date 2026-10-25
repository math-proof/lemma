-- Carved from Lemma/Definitions/Def_IharaLemma_IdempotentSplitting.lean: instance decls only.
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.LinearCombination

namespace IharaLemma


namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B)


instance isMaximal_𝔪 (i : Fin S.n) : (S.𝔪 i).IsMaximal := S.isMaximal i

end IdempotentSplitting


namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)


instance coeOutCornerRing : CoeOut (S.CornerRing i) B := ⟨Subtype.val⟩


section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

instance algebraBaseCornerRing : Algebra 𝒪 (S.CornerRing i) :=
  ((S.toCornerRing i).comp (algebraMap 𝒪 B)).toAlgebra

instance isScalarTower_base_cornerRing : IsScalarTower 𝒪 B (S.CornerRing i) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


end Base


instance isLocalization_cornerRing : IsLocalization (S.𝔪 i).primeCompl (S.CornerRing i) where
  map_units y := by
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem i) (S.𝔪 i) (S.mem_of_isMaximal_of_ne i) y.2
    refine IsUnit.of_mul_eq_one (algebraMap B (S.CornerRing i) t) (Subtype.ext ?_)
    show S.e i * (y : B) * S.e i * (S.e i * t * S.e i) = S.e i
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination (t * (y : B) * (S.e i * S.e i + S.e i + 1)) * h2 + ht
  surj z := by
    obtain ⟨_, a, rfl⟩ := z
    refine ⟨(S.e i * a * S.e i, 1), Subtype.ext ?_⟩
    show S.e i * a * S.e i * (S.e i * ((1 : (S.𝔪 i).primeCompl) : B) * S.e i)
        = S.e i * (S.e i * a * S.e i) * S.e i
    rw [OneMemClass.coe_one]
    ring
  exists_of_eq {x y} h := by
    refine ⟨⟨S.e i, S.notMem i⟩, ?_⟩
    have h' : S.e i * x * S.e i = S.e i * y * S.e i := congrArg Subtype.val h
    show S.e i * x = S.e i * y
    have h2 : S.e i * S.e i = S.e i := (S.idem i).eq
    linear_combination h' + (y - x) * h2

instance isLocalRing_cornerRing : IsLocalRing (S.CornerRing i) :=
  IsLocalization.AtPrime.isLocalRing (S.CornerRing i) (S.𝔪 i)

section CornerModule

variable {M : Type} [AddCommGroup M] [Module B M]


instance smulCornerModule : SMul (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun z m => ⟨(z : B) • (m : M), S.coe_smul_mem i z m⟩⟩


instance moduleCornerModule : Module (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) where
  one_smul m := Subtype.ext (by rw [coe_cornerSmul, coe_one_cornerRing, e_smul_coe])
  mul_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, coe_cornerSmul, coe_cornerSmul, ← mul_smul]; rfl)
  smul_zero x := Subtype.ext (by rw [coe_cornerSmul, ZeroMemClass.coe_zero, smul_zero])
  smul_add x m n := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, smul_add, AddMemClass.coe_add, coe_cornerSmul,
      coe_cornerSmul])
  add_smul x y m := Subtype.ext (by
    rw [coe_cornerSmul, AddMemClass.coe_add, coe_cornerSmul, coe_cornerSmul, ← add_smul]; rfl)
  zero_smul m := Subtype.ext (by
    rw [coe_cornerSmul, coe_zero_cornerRing, zero_smul, ZeroMemClass.coe_zero])

instance isScalarTower_cornerModule :
    IsScalarTower B (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun b z m => Subtype.ext (by
    show (S.e i * b * S.e i * (z : B)) • (m : M) = b • ((z : B) • (m : M))
    rw [mul_assoc, S.e_mul_coe, mul_comm (S.e i) b, mul_assoc, S.e_mul_coe, mul_smul])⟩

end CornerModule


section BaseModule

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]
variable {M : Type} [AddCommGroup M] [Module B M] [Module 𝒪 M] [IsScalarTower 𝒪 B M]

instance isScalarTower_base_cornerModule :
    IsScalarTower 𝒪 (S.CornerRing i) (cornerSubmodule (M := M) (S.e i)) :=
  ⟨fun r z m => by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪 B (S.CornerRing i) r, ← Algebra.smul_def,
      smul_assoc, algebraMap_smul]⟩

end BaseModule

end IdempotentSplitting

end IharaLemma
