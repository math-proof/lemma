module

public import Class.AlgebraicCurve_DivisorPushPull
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois
public import Abbrev.AlgebraicCurve_Correspondence

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

public theorem isScalarTower_along (φ : F →ₐ[K] F') :
    let := algebraAlong φ; IsScalarTower K F F' :=
  let := algebraAlong φ
  IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm


public theorem isIntegral_along (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    let := algebraAlong φ; Algebra.IsIntegral F F' :=
  let := algebraAlong φ
  ⟨hφ⟩

variable (K) in


public theorem isPrincipal_pullbackAlong {D : Divisor K F} (hD : D.IsPrincipal) :
    (pullbackAlong φ hφ D).IsPrincipal := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact Divisor.isPrincipal_pullback hD


public theorem degree_pullbackAlong (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F) :
    degree (pullbackAlong φ hφ D) = (finrankAlong K φ : ℤ) * degree D := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : FundamentalIdentity K F F' := hFI
  exact Divisor.degree_pullback D


public theorem pullbackAlong_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    pullbackAlong φ hφ D ∈ degZero (K := K) (F := F') := by
  rw [mem_degZero, degree_pullbackAlong φ hφ hFI, mem_degZero.mp hD, mul_zero]

end Pullback

section Pushforward

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)


@[simp]
public theorem degree_pushforwardAlong (D : Divisor K F') :
    degree (pushforwardAlong φ hφ D) = degree D := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact Divisor.degree_pushforward D


public theorem pushforwardAlong_mem_degZero {D : Divisor K F'}
    (hD : D ∈ degZero (K := K) (F := F')) :
    pushforwardAlong φ hφ D ∈ degZero (K := K) (F := F) := by
  rwa [mem_degZero, degree_pushforwardAlong]


public theorem isPrincipal_pushforwardAlong (hfin : FiniteAlong K φ)
    (hN : NormFormulaAlong K φ hfin) {D : Divisor K F'} (hD : D.IsPrincipal) :
    (pushforwardAlong φ hφ D).IsPrincipal := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : Module.Finite F F' := hfin
  exact Divisor.isPrincipal_pushforward_of_normFormula hN hD

end Pushforward

end AlongHom

section Correspondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)


public theorem correspondence_apply (D : Divisor K F) :
    correspondence φ ψ hφ hψ D = pushforwardAlong ψ hψ (pullbackAlong φ hφ D) :=
  rfl


public theorem degree_correspondence (hFI : FundamentalIdentityAlong K φ hφ) (D : Divisor K F) :
    Divisor.degree (correspondence φ ψ hφ hψ D) = (finrankAlong K φ : ℤ) * Divisor.degree D := by
  rw [correspondence_apply, degree_pushforwardAlong, degree_pullbackAlong φ hφ hFI]


public theorem correspondence_mem_degZero (hFI : FundamentalIdentityAlong K φ hφ) {D : Divisor K F}
    (hD : D ∈ degZero (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ degZero (K := K) (F := F) :=
  pushforwardAlong_mem_degZero ψ hψ (pullbackAlong_mem_degZero φ hφ hFI hD)


public theorem correspondence_mem_principal (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) {D : Divisor K F}
    (hD : D ∈ principal (K := K) (F := F)) :
    correspondence φ ψ hφ hψ D ∈ principal (K := K) (F := F) :=
  isPrincipal_pushforwardAlong ψ hψ hfin hN (isPrincipal_pullbackAlong φ hφ hD)

end Correspondence

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
variable (hFI : FundamentalIdentityAlong K φ hφ)
variable (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)


@[simp]
public theorem coe_degZeroCorrespondence (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroCorrespondence φ ψ hφ hψ hFI D : Divisor K F) =
      Divisor.correspondence φ ψ hφ hψ (D : Divisor K F) :=
  rfl


public theorem correspondence_mk (D : Divisor.degZero (K := K) (F := F)) :
    correspondence φ ψ hφ hψ hFI hfin hN (mk D) =
      mk (degZeroCorrespondence φ ψ hφ hψ hFI D) :=
  rfl

end Pic0

end AlgebraicCurve

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']


public theorem Place.ord_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    w.ord (φ f) = Place.ramificationIndexAlong φ w * (w.restrictAlong φ hφ).ord f := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact w.ord_restrict f


public theorem Divisor.pullbackAlong_apply [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (D : Divisor K F) (w : Place K F') :
    Divisor.pullbackAlong φ hφ D w
      = Place.ramificationIndexAlong φ w * D (w.restrictAlong φ hφ) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact Divisor.pullback_apply D w


public theorem Divisor.pushforwardAlong_single (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (n : ℤ) :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w n)
      = Finsupp.single (w.restrictAlong φ hφ) (n * w.inertiaDegAlong φ hφ) := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  exact Divisor.pushforward_single w n

end AlongPlaces

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K Z]

namespace Place


public theorem restrictAlong_congr {φ φ' : F →ₐ[K] F₁} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F₁) :
    w.restrictAlong φ hφ = w.restrictAlong φ' hφ' := by
  subst h
  rfl

section Fiber

variable [HasPrincipalDivisors K Z]


@[simp]
public theorem mem_fiberAlong {u : F₁ →ₐ[K] Z} {hu : u.toRingHom.IsIntegral} {w₁ : Place K F₁}
    {W : Place K Z} : W ∈ fiberAlong u hu w₁ ↔ W.restrictAlong u hu = w₁ := by
  let := algebraAlong u
  have := isScalarTower_along u
  have := isIntegral_along u hu
  exact Place.mem_fiber


public theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_single (u : F₁ →ₐ[K] Z)
    (hu : u.toRingHom.IsIntegral) (w₁ : Place K F₁) (n : ℤ) :
    Divisor.pullbackAlong u hu (Finsupp.single w₁ n)
      = ∑ W ∈ fiberAlong u hu w₁,
          Finsupp.single W (n * W.ramificationIndexAlong u) := by
  let := algebraAlong u
  have := isScalarTower_along u
  have := isIntegral_along u hu
  exact Divisor.pullback_single w₁ n

end Fiber

end Place

end AlgebraicCurve

namespace AlgebraicCurve

section AlongTransport

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

variable (K) in


public theorem IntertwinesAlong.inv {ι : F →+* F'} {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (h : IntertwinesAlong ι g g') : IntertwinesAlong ι g⁻¹ g'⁻¹ := fun x => by
  have hx := h (g⁻¹ • x)
  rw [smul_inv_smul] at hx
  rw [← hx, inv_smul_smul]


public theorem IntertwinesAlong.one (ι : F →+* F') :
    IntertwinesAlong ι (1 : SemilinearAut K F) (1 : SemilinearAut K F') := fun x => by
  rw [one_smul, one_smul]


public theorem IntertwinesAlong.mul {ι : F →+* F'} {g₁ g₂ : SemilinearAut K F}
    {g₁' g₂' : SemilinearAut K F'} (h₁ : IntertwinesAlong ι g₁ g₁')
    (h₂ : IntertwinesAlong ι g₂ g₂') : IntertwinesAlong ι (g₁ * g₂) (g₁' * g₂') := fun x => by
  rw [mul_smul, mul_smul, h₂ x, h₁ (g₂ • x)]

end Intertwines

end SemilinearAut

end AlgebraicCurve
