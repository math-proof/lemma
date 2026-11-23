module

public import Class.AlgebraicCurve_DivisorPushPull
public import Instance.AlgebraicCurve_DivisorPushPull
public import Def.AlgebraicCurve_BaseChangeGalois

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

variable (K) in

def FundamentalIdentityAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [HasPrincipalDivisors K F'] : Prop :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  FundamentalIdentity K F F'

variable (K) in

def FiniteAlong (φ : F →ₐ[K] F') : Prop :=
  let := φ.toRingHom.toAlgebra
  Module.Finite F F'

variable (K) in

def NormFormulaAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) : Prop :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Module.Finite F F' := hfin
  Divisor.PushforwardNormFormula K F F'

variable (K) in

def finrankAlong (φ : F →ₐ[K] F') : ℕ :=
  let := φ.toRingHom.toAlgebra
  Module.finrank F F'

end AlongHom

namespace Divisor

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

section Pullback

variable [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pullbackAlong : Divisor K F →+ Divisor K F' :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  Divisor.pullback F'

end Pullback

section Pushforward

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pushforwardAlong : Divisor K F' →+ Divisor K F :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  Divisor.pushforward F

end Pushforward

end AlongHom

section Correspondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

def correspondence : Divisor K F →+ Divisor K F :=
  (pushforwardAlong ψ hψ).comp (pullbackAlong φ hφ)

end Correspondence

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)
variable (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)

def degZeroCorrespondence :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.correspondence φ ψ hφ hψ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => by
      have hD := D.2
      have hpb : Divisor.pullbackAlong φ hφ (D : Divisor K F) ∈
          Divisor.degZero (K := K) (F := F') := by
        rw [Divisor.mem_degZero]
        let := φ.toRingHom.toAlgebra
        have : IsScalarTower K F F' :=
          IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
        have : Algebra.IsIntegral F F' := ⟨hφ⟩
        have : FundamentalIdentity K F F' := hFI
        rw [Divisor.degree_pullback (D : Divisor K F)]
        rw [Divisor.mem_degZero.mp hD, mul_zero]
      rw [Divisor.mem_degZero]
      let := ψ.toRingHom.toAlgebra
      have : IsScalarTower K F F' :=
        IsScalarTower.of_algebraMap_eq fun k => (ψ.commutes k).symm
      have : Algebra.IsIntegral F F' := ⟨hψ⟩
      rw [Divisor.degree_pushforward (Divisor.pullbackAlong φ hφ (D : Divisor K F))]
      exact Divisor.mem_degZero.mp hpb)

def correspondence : Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (degZeroCorrespondence φ ψ hφ hψ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    have hpb : (Divisor.pullbackAlong φ hφ D).IsPrincipal := by
      let := φ.toRingHom.toAlgebra
      have : IsScalarTower K F F' :=
        IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
      have : Algebra.IsIntegral F F' := ⟨hφ⟩
      exact Divisor.isPrincipal_pullback hD
    let := ψ.toRingHom.toAlgebra
    have : IsScalarTower K F F' :=
      IsScalarTower.of_algebraMap_eq fun k => (ψ.commutes k).symm
    have : Algebra.IsIntegral F F' := ⟨hψ⟩
    have : Module.Finite F F' := hfin
    exact Divisor.isPrincipal_pushforward_of_normFormula hN hpb)

end Pic0

end AlgebraicCurve

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def Place.restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    Place K F :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  w.restrict F

def Place.ramificationIndexAlong (φ : F →ₐ[K] F') (w : Place K F') : ℕ :=
  let := φ.toRingHom.toAlgebra
  w.ramificationIndex F

def Place.inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    ℕ :=
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.IsIntegral F F' := ⟨hφ⟩
  w.inertiaDeg F

end AlongPlaces

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K Z]

namespace Place

section Fiber

variable [HasPrincipalDivisors K Z]

def fiberAlong (u : F₁ →ₐ[K] Z) (hu : u.toRingHom.IsIntegral) (w₁ : Place K F₁) :
    Finset (Place K Z) :=
  let := u.toRingHom.toAlgebra
  have : IsScalarTower K F₁ Z := IsScalarTower.of_algebraMap_eq fun k => (u.commutes k).symm
  have : Algebra.IsIntegral F₁ Z := ⟨hu⟩
  Place.fiber Z w₁

end Fiber

end Place

end AlgebraicCurve

namespace AlgebraicCurve

section AlongTransport

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

variable (K) in

def SeparableAlong (φ : F →ₐ[K] F₁) : Prop :=
  let := φ.toRingHom.toAlgebra
  Algebra.IsSeparable F F₁

end AlongTransport

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

section Intertwines

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

def IntertwinesAlong (ι : F →+* F') (g : SemilinearAut K F) (g' : SemilinearAut K F') : Prop :=
  ∀ x : F, g' • (ι x) = ι (g • x)

end Intertwines

end SemilinearAut

end AlgebraicCurve
