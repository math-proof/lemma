import Mathlib
import Lemma.AlgebraicCurve.Correspondence
import Class.WeierstrassCurve_GenusOnePic0

set_option autoImplicit false

noncomputable section IsogenyCurrency

section Delta

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Pic0

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
variable (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)


end Pic0

end AlgebraicCurve

end Delta

open AlgebraicCurve

namespace AlgebraicCurve

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']


end AlgebraicCurve

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable {V W : Affine F} [V.IsElliptic] [W.IsElliptic]
variable [GenusOnePlaceGate V] [AbelTheorem V] [GenusOnePlaceGate W] [AbelTheorem W]
variable (ι : V.FunctionField →ₐ[F] W.FunctionField) (hι : ι.toRingHom.IsIntegral)


variable (hfin : FiniteAlong F ι) (hN : NormFormulaAlong F ι hfin)


end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]

structure IsogenyEndDatum where

  ι : W.FunctionField →ₐ[F] W.FunctionField

  hι : ι.toRingHom.IsIntegral

  hfin : FiniteAlong F ι

namespace IsogenyEndDatum

variable {W}


end IsogenyEndDatum


structure IsogenyHomDatum (V₀ V₁ : Affine F) where
  ι : V₁.FunctionField →ₐ[F] V₀.FunctionField
  hι : ι.toRingHom.IsIntegral
  hfin : FiniteAlong F ι

namespace IsogenyHomDatum

variable {V₀ V₁ : Affine F} [V₀.IsElliptic] [V₁.IsElliptic]
variable [GenusOnePlaceGate V₀] [AbelTheorem V₀] [GenusOnePlaceGate V₁] [AbelTheorem V₁]


end IsogenyHomDatum

end WeierstrassCurve.Affine

end IsogenyCurrency
