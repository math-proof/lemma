import Structure.ModularCurve_ShimuraSubgroup
import Lemma.ModularCurve.ShimuraGenerator
import Lemma.AlgebraicCurve.Correspondence
import Structure.ModularCurve_ShimuraKernel

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
