import Lemma.Definitions.Def_ModularCurve_ShimuraSubgroup
import Lemma.Definitions.Def_ModularCurve_ShimuraGenerator
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Pic0

open Divisor

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)

def pullbackAlongDegZeroHom :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F') :=
  ((Divisor.pullbackAlong φ hφ).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackAlong_mem_degZero φ hφ hFI D.2)

@[simp]
theorem coe_pullbackAlongDegZeroHom (D : Divisor.degZero (K := K) (F := F)) :
    (pullbackAlongDegZeroHom φ hφ hFI D : Divisor K F') =
      Divisor.pullbackAlong φ hφ (D : Divisor K F) :=
  rfl

def pullbackAlongHom : Pic0 K F →+ Pic0 K F' :=
  QuotientAddGroup.map _ _ (pullbackAlongDegZeroHom φ hφ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong φ hφ hD)

theorem pullbackAlongHom_mk (D : Divisor.degZero (K := K) (F := F)) :
    pullbackAlongHom φ hφ hFI (mk D) = mk (pullbackAlongDegZeroHom φ hφ hFI D) :=
  rfl

end Pic0

end AlgebraicCurve

namespace ModularCurve

open AlgebraicCurve IntermediateField

variable (p : ℕ)

abbrev shimuraFunctionFieldBar :
    IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  laurentBaseChange (AlgebraicClosure ℚ) (shimuraFunctionField p)

theorem modularFunctionFieldBar_le_shimuraFunctionFieldBar :
    modularFunctionFieldBar p ≤ shimuraFunctionFieldBar p := by
  show laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)
    ≤ laurentBaseChange (AlgebraicClosure ℚ) (shimuraFunctionField p)
  unfold laurentBaseChange
  exact IntermediateField.adjoin.mono _ _ _
    (Set.image_mono (modularFunctionFieldFull_le_shimuraFunctionField p))

def shimuraInclusion :
    (modularFunctionFieldBar p) →ₐ[AlgebraicClosure ℚ] (shimuraFunctionFieldBar p) :=
  IntermediateField.inclusion (modularFunctionFieldBar_le_shimuraFunctionFieldBar p)

structure ShimuraCoveringInputs : Prop where

  hint : (shimuraInclusion p).toRingHom.IsIntegral

  hpd : HasPrincipalDivisors (AlgebraicClosure ℚ) (shimuraFunctionFieldBar p)

  hFI : haveI := hpd; FundamentalIdentityAlong (AlgebraicClosure ℚ) (shimuraInclusion p) hint

variable {p} in

def shimuraPicardPullback (I : ShimuraCoveringInputs p) :
    JZero p →+ Pic0 (AlgebraicClosure ℚ) (shimuraFunctionFieldBar p) :=
  haveI := I.hpd
  Pic0.pullbackAlongHom (shimuraInclusion p) I.hint I.hFI

variable {p} in

def shimuraKernel (I : ShimuraCoveringInputs p) : AddSubgroup (JZero p) :=
  (shimuraPicardPullback I).ker

end ModularCurve

end
