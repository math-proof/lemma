module

public import Mathlib
public import Def.AlgebraicCurve_Correspondence
public import Class.WeierstrassCurve_GenusOnePic0
public import Structure.Isogeny_ConditionalCurrency
public import Def.WeierstrassCurve_GenusOnePic0

@[expose] public section

set_option autoImplicit false

noncomputable section IsogenyCurrency

section Delta

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Pic0

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)

def pushforwardAlongDegZero :
    Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F'))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφ D.2)

def pushforwardAlongHom : Pic0 K F' →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (pushforwardAlongDegZero φ hφ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong φ hφ hfin hN hD)

end Pic0

end AlgebraicCurve

end Delta

open AlgebraicCurve


namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)

variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)

def pointMapOfPushforward : W.Point →+ V.Point :=
  ((genusOnePic0Equiv V).toAddMonoidHom.comp
      (Pic0.pushforwardAlongHom ι hι hfin hN)).comp
    (genusOnePic0Equiv W).symm.toAddMonoidHom

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]


namespace IsogenyEndDatum

variable {W}

def pointEnd (D : IsogenyEndDatum W) (hN : NormFormulaAlong F D.ι D.hfin) :
    AddMonoid.End W.Point :=
  pointMapOfPushforward D.ι D.hι D.hfin hN

end IsogenyEndDatum

def isogenyEndSubring (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin) :
    Subring (AddMonoid.End W.Point) :=
  Subring.closure (Set.range (fun D => IsogenyEndDatum.pointEnd D (hNs D)))

namespace IsogenyHomDatum

variable {V₀ V₁ : Affine F} [V₀.IsElliptic] [V₁.IsElliptic]
variable [GenusOnePlaceGate V₀] [AbelTheorem V₀] [GenusOnePlaceGate V₁] [AbelTheorem V₁]

def pointHom (D : IsogenyHomDatum V₀ V₁) (hN : NormFormulaAlong F D.ι D.hfin) :
    V₀.Point →+ V₁.Point :=
  pointMapOfPushforward D.ι D.hι D.hfin hN

def ofEndDatum {W' : Affine F} (D : IsogenyEndDatum W') : IsogenyHomDatum W' W' where
  ι := D.ι
  hι := D.hι
  hfin := D.hfin

end IsogenyHomDatum

end WeierstrassCurve.Affine

end IsogenyCurrency

end
